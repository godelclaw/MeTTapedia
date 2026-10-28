-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Source.FreeVars
Layer: Core
Purpose: The free variables of an atom, kept as a named notion for the metatheory. Atoms have no
  binders, so the free variables are exactly the variable occurrences (`Atom.vars`). Also gives the
  closedness (ground) predicate and a small proof about it.
Imports: Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom
Trusted boundary: none
Main exports: freeVars, isGround, isGround_sym
Open obligations: none
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom

namespace Mettapedia.Languages.MeTTa.PLeaTTa.Source

/-- The free variables of `a`. Atoms have no binders, so this is exactly its variable occurrences
    (`Atom.vars`); kept as a named notion because the metatheory reasons about free variables. -/
def freeVars (a : Atom) : List VarName := Atom.vars a

/-- True if `a` is closed (contains no variables), i.e. a *ground* atom. -/
def isGround (a : Atom) : Bool := freeVars a == []

theorem isGround_sym (s : String) : isGround (Atom.sym s) = true := by
  simp [isGround, freeVars, Atom.vars]

end Mettapedia.Languages.MeTTa.PLeaTTa.Source
