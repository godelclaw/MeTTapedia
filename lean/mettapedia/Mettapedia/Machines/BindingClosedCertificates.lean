import Mettapedia.Machines.ContextualCarrierSupport

/-!
# Closed-at-binding certificates in a backtracking store

A cell receives a certificate only when its value is checked at installation.
Earlier cells are never retroactively certified. Immutable binding records
form a stack; retaining a suffix retains every dependency used to earn its
certificates. An unsuccessful finite check is inconclusive, not a refutation.

This models single-assignment bindings and stack rollback. Native trailing,
cell reclamation and moving collection require their own correspondence.
-/
namespace Mettapedia.Machines.BindingClosedCertificates
open ContextualCarrierSupport

variable {Cell : Type} [DecidableEq Cell]

inductive Ground (store : Store Cell) : Term Cell → Prop where
  | literal (flag) : Ground store (.literal flag)
  | boundCell {cell image} : store cell = some image →
      Ground store image → Ground store (.var cell)
  | pair {left right} : Ground store left → Ground store right →
      Ground store (.pair left right)

def Extends (before after : Store Cell) : Prop :=
  ∀ cell image, before cell = some image → after cell = some image

omit [DecidableEq Cell] in
theorem Ground.mono {before after : Store Cell} (stable : Extends before after)
    {term} (ground : Ground before term) : Ground after term := by
  induction ground with
  | literal flag => exact .literal flag
  | boundCell bound _ ih => exact .boundCell (stable _ _ bound) ih
  | pair _ _ ihLeft ihRight => exact .pair ihLeft ihRight

structure Entry (Cell : Type) where
  cell : Cell
  image : Term Cell
  closed : Bool

def store : List (Entry Cell) → Store Cell
  | [], _ => none
  | entry :: rest, cell =>
      if cell = entry.cell then some entry.image else store rest cell

def certified : List (Entry Cell) → Cell → Bool
  | [], _ => false
  | entry :: rest, cell =>
      if cell = entry.cell then entry.closed else certified rest cell

def CacheSound (history : List (Entry Cell)) : Prop :=
  ∀ cell, certified history cell = true →
    ∃ image, store history cell = some image ∧ Ground (store history) image

/-- A concrete conservative checker. Cached success skips the image graph. -/
def check (history : List (Entry Cell)) : Nat → Term Cell → Bool
  | 0, _ => false
  | _ + 1, .literal _ => true
  | fuel + 1, .pair left right => check history fuel left && check history fuel right
  | fuel + 1, .var cell =>
      if certified history cell then true
      else match store history cell with
        | none => false
        | some image => check history fuel image

theorem check_sound (history : List (Entry Cell)) (sound : CacheSound history)
    (fuel : Nat) (term : Term Cell) (accepted : check history fuel term = true) :
    Ground (store history) term := by
  induction fuel generalizing term with
  | zero => simp [check] at accepted
  | succ fuel ih =>
      cases term with
      | literal flag => exact .literal flag
      | pair left right =>
          simp only [check, Bool.and_eq_true] at accepted
          exact .pair (ih left accepted.1) (ih right accepted.2)
      | var cell =>
          by_cases cached : certified history cell = true
          · obtain ⟨image, bound, ground⟩ := sound cell cached
            exact .boundCell bound ground
          · have clear : certified history cell = false := by
              cases h : certified history cell <;> simp_all
            cases bound : store history cell with
            | none => simp [check, clear, bound] at accepted
            | some image =>
                exact .boundCell bound (ih image (by simpa [check, clear, bound] using accepted))

theorem cons_extends (history : List (Entry Cell)) (entry : Entry Cell)
    (fresh : store history entry.cell = none) :
    Extends (store history) (store (entry :: history)) := by
  intro cell image bound
  have different : cell ≠ entry.cell := by
    intro same
    subst cell
    simp [fresh] at bound
  simpa [store, different] using bound

/-- Certificates are earned at installation, from the pre-binding store. -/
def install (history : List (Entry Cell)) (cell : Cell) (image : Term Cell)
    (fuel : Nat) : List (Entry Cell) :=
  ⟨cell, image, check history fuel image⟩ :: history

theorem install_sound (history : List (Entry Cell)) (sound : CacheSound history)
    (cell : Cell) (image : Term Cell) (fuel : Nat)
    (fresh : store history cell = none) :
    CacheSound (install history cell image fuel) := by
  let entry : Entry Cell := ⟨cell, image, check history fuel image⟩
  have stable : Extends (store history) (store (entry :: history)) :=
    cons_extends history entry fresh
  intro query certifiedNow
  by_cases same : query = cell
  · subst query
    have accepted : check history fuel image = true := by
      simpa [install, certified] using certifiedNow
    exact ⟨image, by simp [install, store],
      (check_sound history sound fuel image accepted).mono stable⟩
  · have earlier : certified history query = true := by
      simpa [install, certified, same] using certifiedNow
    obtain ⟨value, bound, ground⟩ := sound query earlier
    exact ⟨value, by simpa [install, store, same] using bound, ground.mono stable⟩

inductive Valid : List (Entry Cell) → Prop where
  | empty : Valid []
  | installed {history cell image fuel} : Valid history →
      store history cell = none → Valid (install history cell image fuel)

theorem valid_sound {history : List (Entry Cell)} (valid : Valid history) :
    CacheSound history := by
  induction valid with
  | empty => intro cell accepted; simp [certified] at accepted
  | installed _ fresh ih => exact install_sound _ ih _ _ _ fresh

/-- Undoing bindings retains already earned certificates, without rechecking
or promoting an earlier binding after one of its dependencies is grounded. -/
theorem drop_valid {history : List (Entry Cell)} (valid : Valid history)
    (count : Nat) : Valid (history.drop count) := by
  induction valid generalizing count with
  | empty => simpa using (Valid.empty (Cell := Cell))
  | @installed history cell image fuel prior fresh ih =>
      cases count with
      | zero => simpa using (Valid.installed prior fresh (image := image) (fuel := fuel))
      | succ count => simpa [install] using ih count

theorem rollback_sound {history : List (Entry Cell)} (valid : Valid history)
    (count : Nat) : CacheSound (history.drop count) :=
  valid_sound (drop_valid valid count)

namespace Controls

def first : List (Entry Nat) := install [] 0 (.var 1) 8
def second : List (Entry Nat) := install first 1 (.literal false) 8
def third : List (Entry Nat) := install second 2 (.pair (.var 0) (.var 1)) 8

theorem histories_valid : Valid third := by
  apply Valid.installed
  · apply Valid.installed
    · apply Valid.installed
      · exact .empty
      · rfl
    · rfl
  · rfl

/-- The later binding may make the value ground, but does not retroactively
certify the earlier binding. Its dependency can still be undone alone. -/
theorem earlier_stays_uncertified : certified second 0 = false := by decide

theorem later_result_certified : certified third 2 = true := by decide

theorem later_result_ground : Ground (store third) (.pair (.var 0) (.var 1)) := by
  obtain ⟨image, bound, ground⟩ := valid_sound histories_valid 2 (by decide)
  have same : image = .pair (.var 0) (.var 1) := by
    simpa [third, install, store] using bound.symm
  simpa [same] using ground

theorem rollback_reopens_dependency : ¬ Ground (store (third.drop 2)) (.var 0) := by
  intro ground
  cases ground with
  | @boundCell cell image bound imageGround =>
      have imageEq : image = Term.var 1 := by
        simpa [third, second, first, install, store] using bound.symm
      subst image
      cases imageGround with
      | boundCell unbound _ => simp [third, second, first, install, store] at unbound

theorem rollback_drops_the_later_certificate :
    certified (third.drop 2) 2 = false := by decide

end Controls
end Mettapedia.Machines.BindingClosedCertificates
