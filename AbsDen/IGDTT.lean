import Lean
import Lean.Parser.Do

namespace IGDTT

open Lean Lean.Parser

universe u
axiom Later : Sort u → Sort u
axiom next {α : Sort u} : α → Later α
axiom ap {α β : Sort u} : Later (α → β) → Later α → Later β
notation "▹ " α:100 => Later α

noncomputable instance : Applicative Later where
  pure := next
  seq f a := ap f (a ())

axiom Later.eq {α : Sort u} (a b : α) : ▹ (a = b) ↔ next a = next b
axiom ap.compute {α β : Sort u} (f : α → β) (a : α) : ap (next f) (next a) = next (f a)
axiom ap.id {α : Sort u} (a : ▹ α) : ap (next id) a = a

axiom gfix {α : Sort u} : (▹ α → α) → ▹ α
axiom gfix.unfold {α : Sort u} (f : ▹ α -> α) : gfix f = next (f (gfix f))

axiom DLater : ▹ (Sort u) → Sort u
axiom DLater.next_eq {α : Sort u} : ▹ α = DLater (next α)
notation "▸ " α:100 => DLater α

declare_syntax_cat nextElem
syntax (name := nextElem) ident Term.optType ppSpace Term.leftArrow term : nextElem
syntax (name := delayedSubst) "next[" nextElem,* "]." term : term
macro_rules
  | `(term| next[]. $e) => `(pure $e)
  | `(term| next[ $x:ident ← $e₁ ]. $e₂) => `(pure (fun $x => $e₂) <*> $e₁)
  | `(term| next[ $x:ident : $t ← $e₁ ]. $e₂) => `(pure (fun $x : $t => $e₂) <*> $e₁)
  | `(term| next[ $x:ident ← $e₁, $es,* ]. $e₂) => `((next[ $es,* ]. (fun $x => $e₂)) <*> $e₁)
  | `(term| next[ $x:ident : $t ← $e₁, $es,* ]. $e₂) => `((next[ $es,* ]. (fun $x : $t => $e₂)) <*> $e₁)
