/- Adapated from `Lean/Meta/Tactic/Simp/RegisterCommand.lean` -/
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Simp.Attr

namespace Aeneas.Simp

open Lean Meta Simp

macro (name := Parser.Command.registerSimpAttr) doc:(docComment)?
  "register_simp_attr'" ext:ident extProc:ident id:ident : command => do
  let str := id.getId.toString
  let idParser := mkIdentFrom id (`Parser.Attr ++ id.getId)
  let descr := quote ((doc.map (·.getDocString) |>.getD s!"simp set for {id.getId.toString}").removeLeadingSpaces)
  let procId := mkIdentFrom id (simpAttrNameToSimprocAttrName id.getId)
  let procStr := procId.getId.toString
  let procIdParser := mkIdentFrom procId (`Parser.Attr ++ procId.getId)
  let procDescr := quote s!"simproc set for {procId.getId.toString}"
  -- TODO: better docDomment for simprocs
  `($[$doc:docComment]? initialize $ext : SimpExtension ← registerSimpAttr $(quote id.getId) $descr $(quote id.getId)
    $[$doc:docComment]? syntax (name := $idParser:ident) $(quote str):str (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? patternIgnore("← " <|> "<- ")? (prio)? : attr
    /-- Simplification procedure -/
    initialize $extProc : SimprocExtension ← registerSimprocAttr $(quote procId.getId) $procDescr none $(quote procId.getId)
    /-- Simplification procedure -/
    syntax (name := $procIdParser:ident) $(quote procStr):str (Parser.Tactic.simpPre <|> Parser.Tactic.simpPost)? : attr)

end Aeneas.Simp
