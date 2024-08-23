import Lean
import Lean.Meta
import Mathlib.Logic.Function.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Closed.Monoidal

namespace TOT

open Lean CategoryTheory CategoryTheory.Category CategoryTheory.Limits

class ISort (SORT : Type u) where
  lift : Sort u → SORT
  imp : SORT → SORT → SORT

notation P " →ᵢ " Q => ISort.imp P Q
notation "(" P ")ᵢ" => ISort.lift P

def IProp := Natᵒᵖ ⥤ Prop
def IType := Natᵒᵖ ⥤ Type

instance : GetElem IProp Nat Prop fun _ _ => True where
  getElem s n _ := s.obj (Opposite.op n)

instance : GetElem IType Nat Type fun _ _ => True where
  getElem s n _ := s.obj (Opposite.op n)

def IProp.validAt (k : Nat) (p : IProp) : Prop := p[k]
def IProp.valid (p : IProp) := ∀ (k:Nat), p[k]

notation:50 k " ⊨ " p:50 => IProp.validAt k p
notation:50 " ⊨ " p:50 => IProp.valid p

--theorem IProp.valid_intro {P : Nat → Prop} {n : Nat} : P n → n ⊨ P :=
--  id
--theorem IProp.valid_elim {P : Nat → Prop} {ρ : Restriction P} {n : Nat} : n ⊨ ⟨P, ρ⟩ → P n := id
--
theorem IProp.valid_monotone_step {P : IProp} {n : Nat} : (n+1) ⊨ P → n ⊨ P :=
  (P.map ((by simp : n ≤ n+1).hom.op)).le

instance functorCategoryHasLimitsOfShape {C : Prop} {J : Type u} [HasLimitsOfShape J C] : HasLimitsOfShape J (K ⥤ C) where
  has_limit F :=
    HasLimit.mk
      { cone := combineCones F fun _ => getLimitCone _
        isLimit := combinedIsLimit _ _ }

instance {C : Type u₁} [Category.{v₁} C] : HasFiniteProducts (C ⥤ Prop) :=
  hasFiniteProducts_of_hasProducts _

instance {C : Type v₁} [SmallCategory C] : CartesianClosed (C ⥤ Prop) :=
  CartesianClosed.mk _
    (fun F => by
      letI := FunctorCategory.prodPreservesColimits F
      have := Presheaf.isLeftAdjoint_of_preservesColimits (prod.functor.obj F)
      exact Exponentiable.mk _ _ (Adjunction.ofIsLeftAdjoint (prod.functor.obj F)))

set_option diagnostics true
#synth HasProducts (Natᵒᵖ ⥤ Type)
#synth CartesianClosed (Natᵒᵖ ⥤ Type)
#check (inferInstance : MonoidalCategory (Natᵒᵖ ⥤ Type))
#check (inferInstance : MonoidalClosed (Natᵒᵖ ⥤ Type))
#check (inferInstance : CartesianClosed (Natᵒᵖ ⥤ Type))
#check (inferInstance : CartesianClosed (Natᵒᵖ ⥤ Prop))
/-
/-- The functor sending `h : Prop` to the constant functor `C ⥤ Prop` sending everything to `h`.
-/
@[simps]
def constProp (J : Type u) [Category J] : Prop ⥤ J ⥤ Prop where
  obj h :=
    { obj := fun _ => h
      map := fun _ => 𝟙 h }
  map f := { app := fun _ => f }

def IProp.lift (h : Prop) : IProp :=
  (constProp Natᵒᵖ).obj h

--instance : ISort IProp where
--  lift := IProp.lift
--  imp := by unfold IProp; exact (fun P Q => Quiver.Hom P Q)

def IType.lift (α : Type) : IType :=
  (Functor.const Natᵒᵖ).obj α

instance : ISort IType where
  lift := IType.lift
  imp := by unfold IType; exact (fun P Q => (ihom P).obj Q)
-/
