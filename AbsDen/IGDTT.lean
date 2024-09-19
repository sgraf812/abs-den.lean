import Lean
import Lean.Parser.Do

namespace IGDTT

open Lean Lean.Parser

universe u

def Laterrr (α : Type u) : Type u := Unit → α
def nexttt {α : Type u} (a : Unit → α) : Laterrr α := a
def appp {α β : Type u} (f : Laterrr (α → β)) (a : Laterrr α) : Laterrr β :=
  fun _ => f () (a ())
unsafe def gfixxx {α : Type u} (f : Laterrr α → α) : α := f (nexttt (fun () => gfixxx f))

-- Generalise from Type u to Sort u:
@[extern "Laterrr"]
axiom Later : Sort u → Sort u
@[extern "nexttt"]
axiom Later.next {α : Sort u} (a : PUnit → α) : Later α
@[extern "appp"]
axiom Later.ap {α β : Sort u} (f : Later (α → β)) (a : Later α) : Later β
@[extern "gfixxx"]
axiom gfix {α : Sort u} (f : Later α → α) : α
axiom gfix.unfold {α : Sort u} (f : Later α -> α) : gfix f = f (Later.next (fun () => gfix f))

notation "▹ " α:100 => Later α

instance : Applicative Later where
  pure a := Later.next (fun () => a)
  seq f a := Later.ap f (a ())

declare_syntax_cat nextElem
syntax (name := nextElem) ident Term.optType ppSpace Term.leftArrow term : nextElem
syntax (name := delayedSubst) "next[" nextElem,* "]." term : term
macro_rules
  | `(term| next[]. $e) => `(Later.next (fun () => $e))
  | `(term| next[ $x:ident ← $e₁ ]. $e₂) => `(Later.ap (next[]. (fun $x => $e₂)) $e₁)
  | `(term| next[ $x:ident : $t ← $e₁ ]. $e₂) => `(Later.ap (next[]. (fun $x : $t => $e₂)) $e₁)
  | `(term| next[ $x:ident ← $e₁, $es,* ]. $e₂) => `(Later.ap (next[ $es,* ]. (fun $x => $e₂)) $e₁)
  | `(term| next[ $x:ident : $t ← $e₁, $es,* ]. $e₂) => `(Later.ap (next[ $es,* ]. (fun $x : $t => $e₂)) $e₁)

axiom Later.eq {α : Sort u} {a b : α} : ▹ (a = b) ↔ (next[].a) = (next[].b)
axiom Later.ap.compute {α β : Sort u} (f : α → β) (a : α) : Later.ap (next[].f) (next[].a) = next[].(f a)
axiom Later.ap.assoc1 {α β : Sort u} (f : α → β) (a : α) : Later.ap (next[].f) (next[].a) = next[].(f a)
axiom Later.ap.assoc2 {α β γ : Sort u} (f : α → β) (g : β → γ) (la : ▹ α) : Later.ap (next[].g) (Later.ap (next[].f) la) = Later.ap (next[]. fun a => g (f a)) la
axiom Later.ap.id {α β : Sort u} (f : α → β) (a : ▹ α) : Later.ap (next[].id) a = a

axiom DLater : ▹ (Sort u) → Sort u
axiom DLater.next_eq {α : Sort u} : ▹ α = DLater (next[].α)
notation "▸ " α:100 => DLater α

-- Some perhaps more controversial definitions:
def flippp {α β : Type u} : (α → Laterrr β) → Laterrr (α → β) :=
  fun f () a => f a ()

@[extern "flippp"]
axiom Later.unsafeFlip {α β : Type u} : (α → Later β) → Later (α → β)
axiom Later.unsafeFlip_eq {α β : Type u} (f : α → Later β) (μ : α) : Later.ap (Later.next (fun () g => g μ)) (Later.unsafeFlip f) = f μ -- I'm reasonably certain that this rule is safe
