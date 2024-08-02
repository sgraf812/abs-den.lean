import AbsDen.LSLR.IProp

import Lean.Elab

namespace LSLR.Tactics
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

meta iintroImp : Tactic := fun stx => do
    -- Extract the current goal
  let mvarId ← getMainGoal
  -- Perform the actual introduction in the goal
  let (fvarId, mvarId') ← Meta.intro1 mvarId
  -- Update the tactic state with the new goal
  replaceMainGoal [mvarId']
  -- Assign the introduced hypothesis a name
  let userName := stx[1].getId
  let lctx ← getLCtx
  let fvarIdUserName ← mkFVarUserName userName
  let newDecl := lctx.get! fvarId
  let newDecl := newDecl.setUserName fvarIdUserName
  modify fun s => { s with lctx := lctx.setDecl newDecl }
  pure unit
elab "iintro" userId:ident : tactic => evalIintro
