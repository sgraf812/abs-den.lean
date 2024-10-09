import Lean
import Lean.Parser.Do

namespace IGDTT

open Lean Lean.Parser

universe u v

-- Generalise from Type u to Sort u:
axiom Later : Sort u → Sort u
@[extern "igdtt_next"]
axiom Later.next {α : Sort u} (a : PUnit → α) : Later α
@[extern "igdtt_ap"]
axiom Later.ap {α : Sort u} {β : Sort v} (f : Later (α → β)) (a : Later α) : Later β
@[extern "igdtt_gfix"]
axiom gfix {α : Sort u} (f : Later α → α) : α
axiom gfix.unfold {α : Sort u} (f : Later α -> α) : gfix f = f (Later.next (fun () => gfix f))

notation "▹ " α:100 => Later α

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
axiom Later.ap.id {α : Sort u} {β : Sort v} (f : α → β) (a : ▹ α) : Later.ap (next[].id) a = a

axiom DLater : ▹ (Sort u) → Sort u
axiom DLater.next_eq {α : Sort u} : ▹ α = DLater (next[].α)
notation "▸ " α:100 => DLater α

-- Some perhaps more controversial definitions:
@[extern "igdtt_flip"]
axiom Later.unsafeFlip {α β : Type u} : (α → Later β) → Later (α → β)
axiom Later.unsafeFlip_eq {α β : Type u} (f : α → Later β) (μ : α) : Later.ap (Later.next (fun () g => g μ)) (Later.unsafeFlip f) = f μ -- I'm reasonably certain that this rule is safe

@[extern "igdtt_force"]
axiom Later.unsafeForce {α : Sort u} : ▹ α → α -- highly unsafe! Need to recall from Barr's work when exactly this is safe. Probably needs support from the typechecker
