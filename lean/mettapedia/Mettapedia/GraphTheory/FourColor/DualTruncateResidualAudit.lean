import Mettapedia.GraphTheory.FourColor.DualTruncateResidualCertificates
import Lean.Util.CollectAxioms

/-! Audit the compact decoder, exact representation adapters and concrete
colouring consumers. Source words are checked inputs; universal existence
and geometric coverage are not asserted. -/

open Lean Elab Command
open Mettapedia.GraphTheory.FourColor
open DualTruncateResidualCertificates

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let roots : List (Name × List Name) := [
    (``CubicRotationByteCertificate.Code.rotation,
      [``CubicRotationByteCertificate.Code.fibre]),
    (``CubicRotationByteCertificate.Code.neighbour_fidelity,
      [``CubicRotationByteCertificate.Code.rotation]),
    (``DualTruncateByteCertificate.Adapter.dartEquiv,
      [``DualTruncateByteCertificate.Adapter.Valid]),
    (``DualTruncateByteCertificate.Adapter.rotation_compatible,
      [``DualTruncateByteCertificate.Adapter.dartEquiv]),
    (``Residual0.target_tait,
      [``Residual0.source_valid, ``Residual0.target_valid,
       ``Residual0.source_word_proper, ``Residual0.adapter_valid,
       ``Residual0.adapter_compatible, ``DualTruncateColoring.colouring]),
    (``Residual1.target_tait,
      [``Residual1.source_valid, ``Residual1.target_valid,
       ``Residual1.source_word_proper, ``Residual1.adapter_valid,
       ``Residual1.adapter_compatible, ``DualTruncateColoring.colouring]),
    (``Residual2.target_tait,
      [``Residual2.source_valid, ``Residual2.target_valid,
       ``Residual2.source_word_proper, ``Residual2.adapter_valid,
       ``Residual2.adapter_compatible, ``DualTruncateColoring.colouring]),
    (``Residual3.target_tait,
      [``Residual3.source_valid, ``Residual3.target_valid,
       ``Residual3.source_word_proper, ``Residual3.adapter_valid,
       ``Residual3.adapter_compatible, ``DualTruncateColoring.colouring]),
    (``Residual4.target_tait,
      [``Residual4.source_valid, ``Residual4.target_valid,
       ``Residual4.source_word_proper, ``Residual4.adapter_valid,
       ``Residual4.adapter_compatible, ``DualTruncateColoring.colouring]),
    (``Residual0.target_supported_route,
      [``Residual0.source_word_proper, ``Residual0.adapter_compatible,
       ``DualTruncateByteCertificate.Adapter.rotation_compatible,
       ``SourceConstructionGSLT.encoded_support_iff]),
    (``Residual1.target_supported_route,
      [``Residual1.source_word_proper, ``Residual1.adapter_compatible,
       ``DualTruncateByteCertificate.Adapter.rotation_compatible,
       ``SourceConstructionGSLT.encoded_support_iff]),
    (``Residual2.target_supported_route,
      [``Residual2.source_word_proper, ``Residual2.adapter_compatible,
       ``DualTruncateByteCertificate.Adapter.rotation_compatible,
       ``SourceConstructionGSLT.encoded_support_iff]),
    (``Residual3.target_supported_route,
      [``Residual3.source_word_proper, ``Residual3.adapter_compatible,
       ``DualTruncateByteCertificate.Adapter.rotation_compatible,
       ``SourceConstructionGSLT.encoded_support_iff]),
    (``Residual4.target_supported_route,
      [``Residual4.source_word_proper, ``Residual4.adapter_compatible,
       ``DualTruncateByteCertificate.Adapter.rotation_compatible,
       ``SourceConstructionGSLT.encoded_support_iff])]
  let forbidden : List Name := [
    `FourColor, `MettapediaFourColor, `Lean.ofReduceBool, `sorryAx]
  let mut inspected : NameSet := {}
  for (root, required) in roots do
    let mut seen : NameSet := {}
    let mut todo := [root]
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if !seen.contains name then
        seen := seen.insert name
        inspected := inspected.insert name
        if let some info := env.find? name then
          todo := info.getUsedConstantsAsSet.toList ++ todo
    for name in required do
      unless seen.contains name do
        throwError m!"Required dependency {name} is absent from {root}"
    for name in seen.toList do
      if forbidden.any (·.isPrefixOf name) then
        throwError m!"Forbidden proof dependency in {root}: {name}"
    let axioms ← liftCoreM <| collectAxioms root
    for name in axioms do
      unless allowed.contains name do
        throwError m!"Unexpected axiom in {root}: {name}"
    logInfo m!"Audited {root}: {axioms.toList}"
  logInfo m!"Dual-and-truncate compact residual certificates: {roots.length} roots; \
    {inspected.toList.length} declarations in the combined dependency closure; \
    complete classical theorem and trust-expanding shortcuts absent."
