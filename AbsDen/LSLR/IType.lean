import AbsDen.LSLR.IProp
import Mathlib.Logic.Function.Defs

namespace LSLR

def IType (α : Type) := α → IProp
notation x " ∈ᵢ " τ => τ x

def True1 : IType α := fun _ => IProp.lift True

def IType.eq {α : Type} (τ₁ : IType α) (τ₂ : IType α) : IProp :=
  ∀ᵢ (x : α), (x ∈ᵢ τ₁) ↔ᵢ (x ∈ᵢ τ₂)

notation τ₁ " ≈ᵢ " τ₂ => IType.eq τ₁ τ₂

def IType.contractive (α : Type) (f : IType α → IType α) : Prop :=
  ∀ τ₁ τ₂, ⊨ (▸(τ₁ ≈ᵢ τ₂)) →ᵢ (f τ₁) ≈ᵢ (f τ₂)

def IType.pow {α : Type} (f : IType α → IType α) (n : Nat) (τ₀ : IType α) : IType α :=
  match n with
  | 0 => τ₀
  | n+1 => f (IType.pow f n τ₀)

def IType.fix_def (α : Type) (f : IType α → IType α) x n :=
  n ⊨ x ∈ᵢ f (IType.pow f n True1)

theorem IType.fix_eq_above (α : Type) (f : IType α → IType α) (hcon : IType.contractive α f) :
∀ k n m, k ⊨ f (IType.pow f (k + n) True1) ≈ᵢ f (IType.pow f (k+m) True1) := by
  intro k n m
  induction k with
  | zero => exact (hcon _ _ _ _ Nat.le.refl ILater.zero)
  | succ k hind2 =>
    apply (hcon _ _ _ _ Nat.le.refl)
    apply ILater.shift.mp
    rw [Nat.add_right_comm k 1 n]
    rw [Nat.add_right_comm k 1 m]
    exact hind2

-- theorem IType.fix_eq_above2 (α : Type) (f : IType α → IType α) (hcon : IType.contractive α f) :
-- ∀ k n m, k ≤ n → k ≤ m → k ⊨ f (IType.pow f n True1) ≈ᵢ f (IType.pow f m True1) := by
--   intro k n m hn hm
--   have ⟨n₁, hn₁⟩ := Nat.le.dest hn
--   have ⟨m₁, hm₁⟩ := Nat.le.dest hm
--   rw [← hn₁]
--   rw [← hm₁]
--   exact fix_eq_above α f hcon k n₁ m₁

def IType.fix {α : Type} (f : IType α → IType α) (hcon : IType.contractive α f) : IType α :=
  let closed x : downClosed (IType.fix_def α f x) := by
    intro n
    have hprev : n ⊨ ▸(pow f (n+1) True1 ≈ᵢ pow f n True1)  := match n with
    | .zero   => ILater.zero
    | .succ n => ILater.shift.mp (fix_eq_above α f hcon n 1 0)
    have heq : n ⊨ (x ∈ᵢ f (pow f (n+1) True1)) ↔ n ⊨ x ∈ᵢ f (pow f n True1) := by
      apply IIff.elim_refl
      apply IImp.elim_refl (hcon _ _ _) hprev
    intro (h : n + 1 ⊨ x ∈ᵢ f (IType.pow f (n + 1) True1))
    have h : n ⊨ x ∈ᵢ f (IType.pow f (n + 1) True1) := IProp.valid_monotone_step h
    show     n ⊨ x ∈ᵢ f (IType.pow f n True1)
    exact heq.mp h
  fun x => ⟨IType.fix_def α f x, closed x⟩

def IType.arrow {α β : Type} (τ₁ : IType α) (τ₂ : IType β) : IType (α → β) :=
  fun f => ⟨fun n => n ⊨ ∀ᵢ a, (a ∈ᵢ τ₁) →ᵢ (f a ∈ᵢ τ₂), _⟩

universe u
def downClosed2 (p : Nat → Type u) : Type u := (n : Nat) → Σ (ι : p (n+1) → p n) (Function.Injective ι)

structure ITy where
  mk ::
  fam : Nat → Sort u
  restrict : fam (n+1) → fam n
  restrict_inj : ∀ n, Function.Injective (@restrict n)
