axiom Set : Type

axiom Elem : Set -> Set -> Prop
infix:50 " ∈ " => Elem

axiom extensionality : ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y

axiom empty_set : ∃ x, ∀ y, ¬ y ∈ x
noncomputable def empty := empty_set.choose
theorem empty_ax : ∀ y, ¬ y ∈ empty := empty_set.choose_spec

axiom pair_set : ∀ x y, ∃ p, ∀ z, z ∈ p ↔ z = x ∨ z = y
noncomputable def pair (x y : Set) := (pair_set x y).choose
theorem pair_ax (x y : Set) : ∀ z, z ∈ pair x y ↔ z = x ∨ z = y := (pair_set x y).choose_spec

def subset (x y : Set) : Prop := ∀ z, z ∈ x → z ∈ y
infix:50 " ⊆ " => subset

-- axiom binary_union : Set → Set → Set
-- infix:50 " ∪ₛ " => binary_union
-- axiom binary_union_def : ∀ x y z, z ∈ (x ∪ₛ y) ↔ z ∈ x ∨ z ∈ y

axiom union_set : ∀ x, ∃ y, ∀ z, (z ∈ y ↔ ∃ u, (z ∈ u ∧ u ∈ x))
noncomputable def union' (x : Set) := (union_set x).choose
theorem union_ax (x : Set) : ∀ z, (z ∈ (union' x) ↔ ∃ u, (z ∈ u ∧ u ∈ x)) := (union_set x).choose_spec
noncomputable def binary_union (x y : Set) : Set := union' (pair x y)
infix:50 " ∪ₛ " => binary_union
theorem binary_union_def (x y z : Set) : z ∈ (x ∪ₛ y) ↔ (z ∈ x ∨ z ∈ y) := by
  unfold binary_union
  rw [union_ax]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h
    obtain ⟨hu₁, hu₂⟩ := hu
    have hu₃ := (pair_ax x y u).mp hu₂
    cases hu₃ with
    | inl hu₃ => exact Or.inl (hu₃ ▸ hu₁)
    | inr hu₃ => exact Or.inr (hu₃ ▸ hu₁)
  · intro h
    cases h with
    | inl h =>
      exists x
      exact ⟨h, (pair_ax x y x).mpr (Or.inl rfl)⟩
    | inr h =>
      exists y
      exact ⟨h, (pair_ax x y y).mpr (Or.inr rfl)⟩

-- Theorem

theorem empty_unique : ∀ e₁ e₂, (∀ x, ¬ x ∈ e₁) → (∀ x, ¬ x ∈ e₂) -> e₁ = e₂ := by
  intro e₁ e₂ h₁ h₂
  apply extensionality
  intro z
  constructor
  · intro hz
    exact absurd hz (h₁ z)
  · intro hz
    exact absurd hz (h₂ z)

theorem pair_comm : ∀ x y, pair x y = pair y x := by
  intro x y
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

theorem subset_trans : ∀ x y z, x ⊆ y → y ⊆ z → x ⊆ z := by
  intro x y z h₁ h₂ u h₃
  exact (h₂ u) ((h₁ u) h₃)

theorem empty_subset : ∀ x, empty ⊆ x := by
  intro x y h
  exact absurd h (empty_ax y)

theorem union_empty : ∀ x, (x ∪ₛ empty) = x := by
  intro x
  apply extensionality
  intro z
  rw [binary_union_def]
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact absurd h (empty_ax z)
  · intro h
    exact Or.inl h
