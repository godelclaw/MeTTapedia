import Mettapedia.DocText.CognitiveArchitectureReadmeCompositional

open Mettapedia.DocText.CognitiveArchitectureReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/CognitiveArchitecture/README.md" cognitiveArchitectureReadmeMarkdown
