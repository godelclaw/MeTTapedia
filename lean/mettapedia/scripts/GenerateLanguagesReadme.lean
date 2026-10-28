import Mettapedia.DocText.LanguagesReadmeCompositional

open Mettapedia.DocText.LanguagesReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/Languages/README.md" languagesReadmeMarkdown
