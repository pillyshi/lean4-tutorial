axiom Set : Type

axiom Elem : Set → Set → Prop
infix:50 " ∈ " => Elem

axiom extensionality : ∀ x y, (∀ z, z ∈ x ↔ z ∈ x) → x = y

axiom empty_set : ∃ e, ∀ x, ¬ x ∈ e
noncomputable def empty : Set := empty_set.choose
theorem empty_ax : ∀ x, ¬ x ∈ empty := empty_set.choose_spec

axiom pair_set : ∀ x y, ∃ p, ∀ z, z ∈ p ↔ z = x ∨ z = y
noncomputable def pair (x y : Set) : Set := (pair_set x y).choose
theorem pair_ax (x y : Set) : ∀ z, z ∈ (pair x y) ↔ z = x ∨ z = y := (pair_set x y).choose_spec

axiom union_set : ∀ x, ∃ y, ∀ z, (z ∈ y ↔ ∃ u, z ∈ u ∧ u ∈ x)
noncomputable def union (x : Set) := (union_set x).choose
theorem union_ax (x : Set) : ∀ z, (z ∈ (union x) ↔ ∃ u, z ∈ u ∧ u ∈ x) := (union_set x).choose_spec
noncomputable def binary_union (x y : Set) : Set := union (pair x y)
infix:50 " ∪ " => binary_union
theorem binary_union_def (x y : Set) : ∀ z, z ∈ (x ∪ y) ↔ z ∈ x ∨ z ∈ y := by
  intro z
  unfold binary_union
  rw [union_ax]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h
    obtain ⟨hu1, hu2⟩ := hu
    have h2 := (pair_ax x y u).mp hu2
    cases h2 with
    | inl h2 => exact Or.inl (h2 ▸ hu1)
    | inr h2 => exact Or.inr (h2 ▸ hu1)
  · intro h
    cases h with
    | inl h =>
      exists x
      exact ⟨h, (pair_ax x y x).mpr (Or.inl rfl)⟩
    | inr h =>
      exists y
      exact ⟨h, (pair_ax x y y).mpr (Or.inr rfl)⟩

axiom separation_set : ∀ x, ∀ (φ : Set -> Prop), ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ φ z
noncomputable def separation (x : Set) (φ : Set -> Prop) : Set := (separation_set x φ).choose
theorem separation_ax (x : Set) (φ : Set -> Prop) : ∀ z, z ∈ (separation x φ) ↔ z ∈ x ∧ φ z := (separation_set x φ).choose_spec
noncomputable def inter (x y : Set) : Set := separation x (fun z => z ∈ y)
infix:50 " ∩ " => inter
theorem inter_def (x y : Set) : ∀ z, z ∈ (x ∩ y) ↔ z ∈ x ∧ z ∈ y := by
  intro z
  unfold inter
  rw [separation_ax]
