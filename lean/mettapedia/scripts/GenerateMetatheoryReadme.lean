import Mettapedia.DocText.MetatheoryReadmeCompositional

open Mettapedia.DocText.MetatheoryReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/Metatheory/README.md" metatheoryReadmeMarkdown
