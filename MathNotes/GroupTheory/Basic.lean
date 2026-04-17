import Mathlib

theorem unique_identity : ∀ e e', (he : ∀)

#check Group
#check One.one

class Semigroup' (G : Type*) extends Mul G where
  protected mul_assoc' : ∀ a b c : G, a * b * c = a * (b * c)

class AddSemigroup' (G : Type*) extends Add G where
  protected add_assoc' : ∀ a b c : G, a + b + c = a + (b + c)

instance : Semigroup' Nat where
  mul := Nat.mul
  mul_assoc' := by
    intro a b c
    simp [Nat.mul_assoc]

instance : AddSemigroup' Nat where
  add := Nat.add
  add_assoc' a b c := by
    simp [Nat.add_assoc]
