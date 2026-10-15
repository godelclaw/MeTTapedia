import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeReadout
import Mettapedia.OSLF.Syntax.SortedCommutativeGroundFactorAllSorts
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Range

/-!
# Finite complete argument readings at each administrative body

Every coordinate of an actual ask, get or build body has a genuine typed
one-hole context recovering that whole body. Complete ground factor
finiteness therefore bounds the whole dependent tuple of coordinate classes.
The resulting finite output range retains every ordered proper-Cut
partition, even when those partitions have the same AC1 body. The signature
and the supplied occurrence-origin carrier may both be infinite.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.ArgumentFibres

open Mettapedia.OSLF.SortedCommutative
open Mettapedia.OSLF.SortedCommutative.GroundFactors

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

def probeHead : Probe source Parallel → SourceHead source Parallel
  | .ask head => head
  | .get head _ => head
  | .build head => head

def bodyAt (instrument : Probe source Parallel) (arguments : Arguments (probeHead instrument)) :
    Value (receiver instrument) :=
  match instrument with
  | .ask head => sourceNode head arguments
  | .get head _ => bundle head arguments
  | .build head => bundle head arguments

def outputAt (instrument : Probe source Parallel) (arguments : Arguments (probeHead instrument)) :
    Value (result instrument) :=
  match instrument with
  | .ask head => bundle head arguments
  | .get _ position => arguments position
  | .build head => sourceNode head arguments

def sourceChildContext (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) :
    RawContext (signature source Parallel) NativeParallel
      (.original (headInput head position)) (.original (headOutput head)) := by
  cases head with
  | ordinary constructor =>
    exact RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
      (Constructor.original constructor) position (fun other _ => arguments other) .hole
  | properCut sort parallel =>
    exact Fin.cases (.left parallel .hole (arguments 1))
      (fun _ => .right parallel (arguments 0) .hole) position
  | unit => exact Fin.elim0 position

private theorem frame_child_fill (constructor : (signature source Parallel).Constructor)
    (arguments : (position : Fin ((signature source Parallel).arity constructor)) →
      Value ((signature source Parallel).input constructor position))
    (position : Fin ((signature source Parallel).arity constructor)) :
    (RawContext.frame constructor position (fun other _ => arguments other) .hole).fill
        (arguments position) = Term.node constructor arguments := by
  apply congrArg (Term.node constructor)
  funext other
  by_cases same : other = position
  · subst other
    simp only [RawContext.fill, RawContext.insert, dite_true]
  · simp only [RawContext.fill, RawContext.insert, dif_neg same]

theorem sourceChildContext_fill (head : SourceHead source Parallel) (arguments : Arguments head)
    (position : Fin (headArity head)) :
    (sourceChildContext head arguments position).fill (arguments position) = sourceNode head arguments := by
  cases head with
  | ordinary constructor => exact frame_child_fill (Constructor.original constructor) arguments position
  | properCut sort parallel => fin_cases position <;> rfl
  | unit => exact Fin.elim0 position

def bodyChildContext (instrument : Probe source Parallel) (arguments : Arguments (probeHead instrument))
    (position : Fin (headArity (probeHead instrument))) :
    RawContext (signature source Parallel) NativeParallel
      (.original (headInput (probeHead instrument) position)) (receiver instrument) :=
  match instrument with
  | .ask head => sourceChildContext head arguments position
  | .get head _ => RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
      (Constructor.arguments head) position (fun other _ => arguments other) .hole
  | .build head => RawContext.frame (signature := signature source Parallel) (Parallel := NativeParallel)
      (Constructor.arguments head) position (fun other _ => arguments other) .hole

theorem bodyChildContext_fill (instrument : Probe source Parallel)
    (arguments : Arguments (probeHead instrument)) (position : Fin (headArity (probeHead instrument))) :
    (bodyChildContext instrument arguments position).fill (arguments position) = bodyAt instrument arguments := by
  cases instrument with
  | ask head => exact sourceChildContext_fill head arguments position
  | get head selected => exact frame_child_fill (Constructor.arguments head) arguments position
  | build head => exact frame_child_fill (Constructor.arguments head) arguments position

abbrev ClassArguments (head : SourceHead source Parallel) :=
  (position : Fin (headArity head)) →
    ValueClass (source := source) (Parallel := Parallel) (.original (headInput head position))

def classSourceNode (head : SourceHead source Parallel) (arguments : ClassArguments head) :
    ValueClass (source := source) (Parallel := Parallel) (.original (headOutput head)) := by
  cases head with
  | ordinary constructor => exact (Head.node (signature := signature source Parallel)
      (Parallel := NativeParallel) (Constructor.original constructor) arguments).class
  | properCut sort parallel => exact classCut parallel (arguments 0) (arguments 1)
  | unit sort parallel => exact classOf (.zero parallel)

def classBundle (head : SourceHead source Parallel) (arguments : ClassArguments head) :
    ValueClass (source := source) (Parallel := Parallel) (.arguments head) :=
  (Head.node (signature := signature source Parallel) (Parallel := NativeParallel)
    (Constructor.arguments head) arguments).class

theorem classSourceNode_readout (head : SourceHead source Parallel) (arguments : Arguments head) :
    classSourceNode head (fun position => classOf (arguments position)) = classOf (sourceNode head arguments) := by
  cases head with
  | ordinary constructor =>
    exact Head.class_node (signature := signature source Parallel)
      (Parallel := NativeParallel) (Constructor.original constructor) arguments
  | properCut => rfl
  | unit => rfl

theorem classBundle_readout (head : SourceHead source Parallel) (arguments : Arguments head) :
    classBundle head (fun position => classOf (arguments position)) = classOf (bundle head arguments) :=
  Head.class_node (signature := signature source Parallel) (Parallel := NativeParallel)
    (Constructor.arguments head) arguments

def classOutput (instrument : Probe source Parallel) (arguments : ClassArguments (probeHead instrument)) :
    ValueClass (source := source) (Parallel := Parallel) (result instrument) :=
  match instrument with
  | .ask head => classBundle head arguments
  | .get _ position => arguments position
  | .build head => classSourceNode head arguments

theorem classOutput_readout (instrument : Probe source Parallel)
    (arguments : Arguments (probeHead instrument)) :
    classOutput instrument (fun position => classOf (arguments position)) = classOf (outputAt instrument arguments) := by
  cases instrument with
  | ask head => exact classBundle_readout head arguments
  | get => rfl
  | build head => exact classSourceNode_readout head arguments

abbrev ArgumentCode (instrument : Probe source Parallel)
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)) :=
  (position : Fin (headArity (probeHead instrument))) →
    Factor (signature := signature source Parallel) (Parallel := NativeParallel)
      (Srt.original (headInput (probeHead instrument) position)) body

theorem argumentCode_finite (instrument : Probe source Parallel)
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)) :
    Finite (ArgumentCode instrument body) := by
  let _ : ∀ position : Fin (headArity (probeHead instrument)),
      Finite (Factor (signature := signature source Parallel) (Parallel := NativeParallel)
        (Srt.original (headInput (probeHead instrument) position)) body) :=
    fun position => factor_finite _ body
  exact inferInstance

def codeOutput (instrument : Probe source Parallel)
    {body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)}
    (code : ArgumentCode instrument body) :
    ValueClass (source := source) (Parallel := Parallel) (result instrument) :=
  classOutput instrument (fun position => (code position).val.2)

def argumentCode (instrument : Probe source Parallel)
    (arguments : Arguments (probeHead instrument))
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (read : classOf (bodyAt instrument arguments) = body) : ArgumentCode instrument body :=
  fun position =>
    ⟨(normalizeContext (contextClassOf (bodyChildContext instrument arguments position)),
      classOf (arguments position)),
      (ContextClass.normalize_filling (contextClassOf (bodyChildContext instrument arguments position))
        (classOf (arguments position))).trans
        ((congrArg classOf (bodyChildContext_fill instrument arguments position)).trans read)⟩

theorem argumentCode_output_readout (instrument : Probe source Parallel)
    (arguments : Arguments (probeHead instrument))
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument))
    (read : classOf (bodyAt instrument arguments) = body) :
    codeOutput instrument (argumentCode instrument arguments body read) =
      classOf (outputAt instrument arguments) :=
  classOutput_readout instrument arguments

theorem outputs_finite_at_body (instrument : Probe source Parallel)
    (body : ValueClass (source := source) (Parallel := Parallel) (receiver instrument)) :
    Set.Finite {output : ValueClass (source := source) (Parallel := Parallel) (result instrument) |
      ∃ arguments : Arguments (probeHead instrument),
        classOf (bodyAt instrument arguments) = body ∧ classOf (outputAt instrument arguments) = output} := by
  let _ := argumentCode_finite instrument body
  apply (Set.finite_range (codeOutput instrument (body := body))).subset
  rintro output ⟨arguments, read, rfl⟩
  exact ⟨argumentCode instrument arguments body read, argumentCode_output_readout instrument arguments body read⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments.ArgumentFibres
