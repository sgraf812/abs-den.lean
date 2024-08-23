import AbsDen.LSLR.IProp

import Lean.Elab

namespace LSLR.Tactics
open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta

syntax (name := iintro) "iintro" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[tactic iintro]
def evalIntro : Tactic := fun stx => do
  match stx with
  | `(tactic| iintro)                   => iintroStep none `_
  | `(tactic| iintro $h:ident)          => iintroStep h h.getId
  | `(tactic| iintro _%$tk)             => iintroStep tk `_
  /- Type ascription -/
  | `(tactic| iintro ($h:ident : $type:term)) => iintroStep h h.getId type
  /- We use `@h` at the match-discriminant to disable the implicit lambda feature -/
  | `(tactic| iintro $pat:term)         => evalTactic (← `(tactic| iintro h; match @h with | $pat:term => ?_; try clear h))
  | `(tactic| iintro $h:term $hs:term*) => evalTactic (← `(tactic| iintro $h:term; iintro $hs:term*))
  | _ => throwUnsupportedSyntax
where
  iintroStep (ref : Option Syntax) (n : Name) (typeStx? : Option Syntax := none) : TacticM Unit := do
    let fvarId ← liftMetaTacticAux fun mvarId => do
      let (fvarId, mvarId) ← mvarId.intro n
      pure (fvarId, [mvarId])
    if let some typeStx := typeStx? then
      withMainContext do
        let type ← Term.withSynthesize (postpone := .yes) <| Term.elabType typeStx
        let fvar := mkFVar fvarId
        let fvarType ← inferType fvar
        unless (← isDefEqGuarded type fvarType) do
          throwError "type mismatch at `iintro {fvar}`{← mkHasTypeButIsExpectedMsg fvarType type}"
        liftMetaTactic fun mvarId => return [← mvarId.replaceLocalDeclDefEq fvarId type]
    if let some stx := ref then
      withMainContext do
        Term.addLocalVarInfo stx (mkFVar fvarId)

theorem test {P Q : IProp} {n:Nat} : n ⊨ (P →ᵢ Q) := by
  -- intro k _ p
  apply IImp.intro
  intro k l h
  apply (IProp.valid_monotone l)
  refine blah
  clear l n

  rename k
