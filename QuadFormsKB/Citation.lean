/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Citation attribute

Citation attribute: tags a declaration with a bibliography key from references.bib and a locator.

    @[kb "cassels1978" "Ch. 6, Lemma 2.1"]
    theorem foo : ... := ...

The first string is a key of `references.bib`; the second, optional, string is a locator
inside that source (chapter, section, theorem number, page). The attribute only records the
citation; whether a declaration is proved is decided by the Lean kernel, not by the tag.
-/

namespace QuadFormsKB

open Lean

/-- One citation entry: a declaration plus its literature citation. -/
structure KBTag where
  decl : Name
  source : String
  locator : String
  deriving Inhabited, Repr

initialize kbExt : SimplePersistentEnvExtension KBTag (Array KBTag) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

/-- `@[kb "source" "locator"]` records a literature citation for a declaration. -/
syntax (name := kbAttr) "kb " str (ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `kbAttr
  descr := "Tag a declaration with a literature citation (a references.bib key and a locator)"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == AttributeKind.global do
      throwError "the kb attribute must be global"
    match stx with
    | `(attr| kb $src:str $[$loc:str]?) =>
      modifyEnv fun env => kbExt.addEntry env
        { decl, source := src.getString, locator := (loc.map (·.getString)).getD "" }
    | _ => Elab.throwUnsupportedSyntax
}

/-- All tagged declarations visible in `env` (imported and local). -/
def kbEntries (env : Environment) : Array KBTag :=
  kbExt.getState env

end QuadFormsKB
