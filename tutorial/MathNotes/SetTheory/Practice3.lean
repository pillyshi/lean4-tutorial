namespace ZFC

axiom Set : Type

axiom Elem : Set -> Set -> Prop
infix:50 " ∈ " => Elem

axiom extensionality : ∀ x y, (∀ w, w ∈ x ↔ w ∈ y) → x = y

axiom empty_set : ∃ x, ∀ y, ¬ y ∈ x
noncomputable def empty : Set := empty_set.choose
theorem empty_ax : ∀ x, ¬ x ∈ empty := empty_set.choose_spec

axiom pair_set : ∀ x y : Set, ∃ p : Set, ∀ z, z ∈ p ↔ z = x ∨ z = y
noncomputable def pair (x y : Set) : Set := (pair_set x y).choose
theorem pair_ax (x y : Set) : ∀ z, z ∈ pair x y ↔ z = x ∨ z = y := (pair_set x y).choose_spec

def subset (x y : Set) : Prop := ∀ z, z ∈ x → z ∈ y
infix:50 " ⊆ " => subset

axiom binary_union : Set -> Set -> Set
scoped infix:50 " ∪ₛ " => binary_union
axiom binary_union_def : ∀ x y z : Set, z ∈ (x ∪ₛ y) ↔ z ∈ x ∨ z ∈ y

-- Theorem
theorem empty_unique : ∀ e₁ e₂, (∀ x, ¬ x ∈ e₁) → (∀ x, ¬ x ∈ e₂) → e₁ = e₂ := by
  intro e₁ e₂ h₁ h₂
  apply extensionality
  intro w
  constructor
  · intro hw
    exact absurd hw (h₁ w)
  · intro hw
    exact absurd hw (h₂ w)

theorem pair_comm (x y : Set) : pair x y = pair y x := by
  apply extensionality
  intro w
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

theorem subset_trans (x y z : Set) : x ⊆ y → y ⊆ z → x ⊆ z := by
  intro h₁ h₂ a h₃
  -- h₁ a : a ∈ x → a ∈ y
  -- h₂ a : a ∈ y → a ∈ z
  exact  (h₂ a) ((h₁ a) h₃)

theorem empty_subset (x : Set) : empty ⊆ x := by
  -- ∀ y, y ∈ empty → y ∈ x
  intro y h
  exact absurd h (empty_ax y)

theorem union_empty (x : Set) : (x ∪ₛ empty) = x := by
  apply extensionality
  intro w
  rw [binary_union_def]
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact absurd h (empty_ax w)
  · intro h
    exact Or.inl h

end ZFC
