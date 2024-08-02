import Lean
import Lean.Meta
import Mathlib.Logic.Function.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types

namespace TOT
open Lean CategoryTheory

def IProp := Natᵒᵖ ⥤ Prop
def IType.{u} := Natᵒᵖ ⥤ Type u

instance : GetElem (ISort u) Nat (Sort u) fun _ _ => True where
  getElem s n _ := s.fam n

structure Restriction (fam : Nat → Sort u) : Sort (u+1) :=
  mk ::
  restrict : (n : Nat) → fam (n+1) → fam n
  inj : Function.Injective (restrict n)

def Restriction.mkProp (fam : Nat → Prop) (r : (n:Nat) → fam (n+1) → fam n) : Restriction fam :=
  ⟨r, by intro _ _ _ _; trivial⟩

structure ISort (u : Univ) : Sort (u+1) where
  mk ::
  fam : Nat → Sort u
  restr : Restriction fam

instance : GetElem (ISort u) Nat (Sort u) fun _ _ => True where
  getElem s n _ := s.fam n

abbrev IProp := ISort 0
abbrev IType u := ISort (u+1)

def IProp.validAt (k : Nat) (p : IProp) : Prop := p[k]
def IProp.valid (p : IProp) := ∀ (k:Nat), p[k]

notation:50 k " ⊨ " p:50 => IProp.validAt k p
notation:50 " ⊨ " p:50 => IProp.valid p

theorem IProp.valid_intro {P : Nat → Prop} {ρ : Restriction P} {n : Nat} : P n → n ⊨ ⟨P, ρ⟩ := id
theorem IProp.valid_elim {P : Nat → Prop} {ρ : Restriction P} {n : Nat} : n ⊨ ⟨P, ρ⟩ → P n := id

theorem IProp.valid_monotone_step {P : IProp} {n : Nat} : (n+1) ⊨ P → n ⊨ P := by
  intro h_succ
  apply IProp.valid_intro
  exact (P.restr.restrict n h_succ)

def ISort.lift (α : Sort u) : ISort u :=
  ⟨fun _ => α, ⟨fun _n a => a, by intro _ _ _ _; trivial⟩⟩

notation "(" s ")ᵢ" => ISort.lift s

--------------------------

def IArrow (α β : ISort u) : ISort u :=
  ⟨fun n => { f : α[n] → β[n] // f ∘ α.restr.restrict n = β.restr.restrict n ∘ f }, fun _ h k h_le => h k h_le.step⟩

notation P " →ᵢ " Q => IArrow P Q

theorem IArrow.intro {n : Nat} {P Q : ISort u} : (∀ k, k ≤ n → k ⊨ P → k ⊨ Q) → n ⊨ (P →ᵢ Q) :=
  fun h => ISort.valid_intro h

theorem IArrow.elim {n : Nat} {P Q : ISort u} : n ⊨ (P →ᵢ Q) → (∀ k, k ≤ n → k ⊨ P → k ⊨ Q) :=
  fun h => ISort.valid_elim h

theorem IArrow.elim_refl {n : Nat} {P Q : ISort u} : n ⊨ (P →ᵢ Q) → n ⊨ P → n ⊨ Q :=
  fun h => IProp.valid_elim h n Nat.le.refl
