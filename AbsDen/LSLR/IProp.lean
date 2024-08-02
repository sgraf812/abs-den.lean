import Lean
import Lean.Elab
import Lean.Meta.Tactic

namespace LSLR
open Lean

universe u
def downClosed (p : Nat → Prop) : Prop := ∀ n , p (n+1) -> p n

def IProp := { p : Nat → Prop // downClosed p }

def IProp.validAt (k : Nat) (p : IProp) := p.val k
def IProp.valid (p : IProp) := ∀ k, p.validAt k

notation:50 k " ⊨ " p:50 => IProp.validAt k p
notation:50 " ⊨ " p:50 => IProp.valid p

theorem IProp.valid_intro {P : Nat → Prop} {H : downClosed P} {n : Nat} : P n → n ⊨ ⟨P, H⟩ := id
theorem IProp.valid_elim {P : Nat → Prop} {H : downClosed P} {n : Nat} : n ⊨ ⟨P, H⟩ → P n := id

theorem IProp.valid_monotone_step {P : IProp} {n : Nat} : (n+1) ⊨ P → n ⊨ P := by
  intro h_succ
  apply IProp.valid_intro
  exact (P.property n h_succ)

theorem IProp.valid_monotone {P : IProp} {n m : Nat} (h_le : n ≤ m) (h_valid : m ⊨ P) : n ⊨ P := by
  induction h_le
  case refl     => trivial
  case step ind => apply ind (IProp.valid_monotone_step h_valid)

def IProp.lift (α : Prop) : IProp :=
  ⟨fun _ => α, fun _ h => h⟩

notation "(" P ")ᵢ" => IProp.lift P

-------------------------
def IAnd (P : IProp) (Q : IProp) : IProp :=
  ⟨fun k => P.val k ∧ Q.val k, fun k h => And.imp (P.property k) (Q.property k) h⟩
notation P " ∧ᵢ " Q => IAnd P Q

theorem IAnd.intro {n : Nat} {P Q : IProp} : n ⊨ P → n ⊨ Q → n ⊨ (P ∧ᵢ Q) :=
  fun p q => ⟨p, q⟩

theorem IAnd.elim {n : Nat} {P Q : IProp} : n ⊨ (P ∧ᵢ Q) → n ⊨ P ∧ n ⊨ Q :=
  fun ⟨p, q⟩ => ⟨p, q⟩

theorem IAnd.left {n : Nat} {P Q : IProp} : n ⊨ (P ∧ᵢ Q) → n ⊨ P :=
  fun ⟨p, _⟩ => p

theorem IAnd.right {n : Nat} {P Q : IProp} : n ⊨ (P ∧ᵢ Q) → n ⊨ Q :=
  fun ⟨_, q⟩ => q

-- icases/isplit tactic?

-------------------------
def IOr (P : IProp) (Q : IProp) : IProp :=
  ⟨fun k => P.val k ∨ Q.val k, fun k h => Or.imp (P.property k) (Q.property k) h⟩
notation P " ∨ᵢ " Q => IOr P Q

theorem IOr.inl {n : Nat} {P Q : IProp} : n ⊨ P → n ⊨ P ∨ᵢ Q :=
  fun p => Or.inl p

theorem IOr.inr {n : Nat} {P Q : IProp} : n ⊨ Q → n ⊨ P ∨ᵢ Q :=
  fun p => Or.inr p

theorem IOr.elim {n : Nat} {P Q : IProp} : n ⊨ (P ∨ᵢ Q) → n ⊨ P ∨ n ⊨ Q :=
  id

-- ileft/iright tactic?

-------------------------
def IImp (α β : IProp) : IProp :=
  ⟨fun n => ∀ k ≤ n, k ⊨ α → k ⊨ β, fun _ h k h_le => h k h_le.step⟩

notation P " →ᵢ " Q => IImp P Q

theorem IImp.intro {n : Nat} {P Q : IProp} : (∀ k, k ≤ n → k ⊨ P → k ⊨ Q) → n ⊨ (P →ᵢ Q) :=
  fun h => IProp.valid_intro h

theorem IImp.elim {n : Nat} {P Q : IProp} : n ⊨ (P →ᵢ Q) → (∀ k, k ≤ n → k ⊨ P → k ⊨ Q) :=
  fun h => IProp.valid_elim h

theorem IImp.elim_refl {n : Nat} {P Q : IProp} : n ⊨ (P →ᵢ Q) → n ⊨ P → n ⊨ Q :=
  fun h => IProp.valid_elim h n Nat.le.refl

-------------------------
def IIff (α β : IProp) : IProp :=
  ⟨fun n => ∀ k ≤ n, k ⊨ α ↔ k ⊨ β, fun _ h k h_le => h k h_le.step⟩

notation P " ↔ᵢ " Q => IIff P Q

theorem IIff.intro {n : Nat} {P Q : IProp} : (∀ k, k ≤ n → (k ⊨ P ↔ k ⊨ Q)) → n ⊨ (P ↔ᵢ Q) :=
  fun h => IProp.valid_intro h

theorem IIff.intro2 {n : Nat} {P Q : IProp} (mp : n ⊨ P →ᵢ Q) (mpr : n ⊨ Q →ᵢ P) : n ⊨ (P ↔ᵢ Q) := by
  apply IIff.intro
  intro k h
  apply Iff.intro (mp k h) (mpr k h)

theorem IIff.elim {n : Nat} {P Q : IProp} : n ⊨ (P ↔ᵢ Q) → (∀ k, k ≤ n → (k ⊨ P ↔ k ⊨ Q)) :=
  fun h => IProp.valid_elim h

theorem IIff.elim_refl {n : Nat} {P Q : IProp} : n ⊨ (P ↔ᵢ Q) → (n ⊨ P ↔ n ⊨ Q) :=
  fun h => IProp.valid_elim h n Nat.le.refl

-- perhaps new tactic iintros?

-------------------------
def IForall {α : Type u} (p : α → IProp) : IProp :=
  ⟨fun k => ∀ a, (p a).val k, fun k h a => (p a).property k (h a)⟩

notation "∀ᵢ " x ", " P => IForall (fun x => P)

theorem IForall.intro {n : Nat} {α : Type u} {P : α → IProp} : (∀ x : α, (n ⊨ P x)) → (n ⊨ ∀ᵢ x, P x) :=
  id

theorem IForall.elim {n : Nat} {α : Type u} {P : α → IProp} : (n ⊨ ∀ᵢ x, P x) → (∀ x : α, (n ⊨ P x)) :=
  id

-- tactics: iintro?

-------------------------
def IExists {α : Type u} (p : α → IProp) : IProp :=
  ⟨fun k => ∃ a, (p a).val k, fun k ⟨a, h⟩ => ⟨a, (p a).property k h⟩⟩

notation "∃ᵢ " x ", " P => IExists (fun x => P)

theorem IExists.intro {n : Nat} {α : Type u} {P : α → IProp} : (∃ x : α, (n ⊨ P x)) → (n ⊨ ∃ᵢ x, P x) :=
  id

theorem IExists.elim {n : Nat} {α : Type u} {P : α → IProp} : (n ⊨ ∃ᵢ x, P x) → (∃ x : α, (n ⊨ P x)) :=
  id

-- tactics: iexists, idestruct

-------------------------
def ILater (P : IProp) : IProp :=
  ⟨fun | .zero => True | .succ n => P.val n, by
    intro n h
    cases n with
    | zero => trivial
    | succ n => show P.val n; exact P.property n h⟩

notation "▸" P => ILater P

theorem ILater.zero {P : IProp} : 0 ⊨ ▸P :=
  IProp.valid_intro trivial

theorem ILater.intro {P : IProp} : n ⊨ P → n ⊨ ▸P := by
  intro h
  apply IProp.valid_intro
  cases n with
  | zero => trivial
  | succ => exact IProp.valid_monotone_step h

theorem ILater.shift {P : IProp} : n ⊨ P ↔ (n+1) ⊨ ▸P := by
  apply Iff.intro
  · intro h
    apply IProp.valid_intro
    exact h
  · intro h
    apply IProp.valid_intro
    exact h

theorem ILater.loeb_induction {P : IProp} {n : Nat} : n ⊨ ((▸P) →ᵢ P) → (n ⊨ P) := by
  intro h
  induction n with
  | zero   => show 0 ⊨ P; exact (h 0 Nat.le.refl ILater.zero)
  | succ n =>
    rename_i h_ind
    have h_pn : n ⊨ P := by
      apply h_ind
      intros k h_le
      exact h k (Nat.le_add_right_of_le h_le)
    have h_l : (n+1) ⊨ ▸P := ILater.shift.mp h_pn
    show (n+1) ⊨ P; apply h (n+1) Nat.le.refl h_l

-- tactics: iintro_later, later_shift, loeb_induction
