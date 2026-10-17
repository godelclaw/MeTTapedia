import Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule

open Mettapedia.GraphTheory.Representation.EdgeListToMatrixModule

#eval do
  let path := "artifacts/mathematical-representations-strengthening-20261016/EdgeListToMatrix.module"
  IO.FS.writeFile path moduleText
  let actual ← IO.FS.readBinFile path
  unless actual == moduleBytes do
    throw (IO.userError "module file differs from the proved canonical bytes")
  let source ← IO.FS.readFile path
  unless source == moduleText do
    throw (IO.userError "module file differs from the proved canonical text")
  unless (Mettapedia.GSLT.LanguageDef.ModuleFormat.readText?
      Mettapedia.GSLT.LanguageDef.ModuleFormat.upstreamLimits source).isSome do
    throw (IO.userError "module file was not admitted by the reader")
  IO.println s!"Module file round trip passed: {actual.size} bytes"
