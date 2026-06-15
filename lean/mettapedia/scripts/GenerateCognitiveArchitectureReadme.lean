import Mettapedia.DocText.CognitiveArchitectureReadmeCompositional

open Mettapedia.DocText.CognitiveArchitectureReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/Mettapedia/lean/mettapedia/Mettapedia/CognitiveArchitecture/README.md" cognitiveArchitectureReadmeMarkdown
