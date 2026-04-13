axiom Set : Type
axiom Elem : Set -> Set -> Prop

infix:50 " ∈ " => Elem

axiom extensionality : ∀ x y : Set, (∀ z, z ∈ x ↔ z ∈ y) -> x = y

axiom emptySet : ∃ e, ∀ x, ¬ x ∈ e
noncomputable def empty : Set := emptySet.choose
theorem empty_ax : ∀ x, ¬ x ∈ empty := emptySet.choose_spec

axiom pairSet : ∀ x y : Set, ∃ p : Set, ∀ z, z ∈ p ↔ z = x ∨ z = y
noncomputable def pair (x y : Set) : Set := (pairSet x y).choose
theorem pair_ax (x y : Set) : ∀ z, z ∈ pair x y ↔ z = x ∨ z = y := (pairSet x y).choose_spec

theorem empty_unique : ∀ e₁ e₂ : Set,
    (∀ x, ¬ x ∈ e₁) -> (∀ x, ¬ x ∈ e₂) -> e₁ = e₂ := by
  intro e₁ e₂ h₁ h₂
  apply extensionality
  intro z
  constructor
  · intro hz
    exact absurd hz (h₁ z)
  · intro hz
    exact absurd hz (h₂ z)

theorem pair_comm (x y : Set) : pair x y = pair y x := by
  apply extensionality
  intro z
  rw [pair_ax, pair_ax]
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl h
