import Mettapedia.DocText.CogArchReadmeCompositional

open Mettapedia.DocText.CogArchReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/CogArch/README.md" cognitiveArchitectureReadmeMarkdown
