axiom Set : Type

axiom Elem : Set → Set → Prop
infix:50 " ∈ " => Elem

axiom extensionality : ∀ x y, ∀ z, (z ∈ x ↔ z ∈ y) → x = y

axiom empty_set : ∃ x, ∀ y, ¬ y ∈ x
noncomputable def empty : Set := empty_set.choose
theorem empty_ax : ∀ y, ¬ y ∈ empty := empty_set.choose_spec

axiom pair_set : ∀ x y, ∃ z, ∀ u, u ∈ z ↔ u = x ∨ u = y
noncomputable def pair (x y : Set) : Set := (pair_set x y).choose
theorem pair_ax (x y) : ∀ u, u ∈ (pair x y) ↔ u = x ∨ u = y := (pair_set x y).choose_spec

axiom union_set : ∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ u, z ∈ u ∧ u ∈ x
noncomputable def union (x : Set) : Set := (union_set x).choose
theorem union_ax (x : Set) : ∀ z, z ∈ (union x) ↔ ∃ u, z ∈ u ∧ u ∈ x := (union_set x).choose_spec
noncomputable def binary_union (x y : Set) : Set := union (pair x y)
infix:50 " ∪ " => binary_union
theorem binary_union_def (x y : Set) : ∀ z, z ∈ (x ∪ y) ↔ z ∈ x ∨ z ∈ y := by
  unfold binary_union
  intro z
  rw [union_ax]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h
    obtain ⟨hu1, hu2⟩ := hu
    have hu3 := (pair_ax x y u).mp hu2
    cases hu3 with
    | inl hu3 => exact Or.inl (hu3 ▸ hu1)
    | inr hu3 => exact Or.inr (hu3 ▸ hu1)
  · intro h
    cases h with
    | inl h =>
      exists x
      exact ⟨h, (pair_ax x y x).mpr (Or.inl rfl)⟩
    | inr h =>
      exists y
      exact ⟨h, (pair_ax x y y).mpr (Or.inr rfl)⟩

axiom separation_set : ∀ x, ∀ (φ : Set → Prop), ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ φ z
noncomputable def separation (x : Set) (φ : Set → Prop) : Set := (separation_set x φ).choose
theorem separation_ax (x : Set) (φ : Set → Prop) : ∀ z, z ∈ (separation x φ) ↔ z ∈ x ∧ φ z := (separation_set x φ).choose_spec
noncomputable def inter (x y : Set) : Set := separation x (fun z => z ∈ y)
infix:50 " ∩ " => inter
theorem inter_def (x y : Set) : ∀ z, z ∈ (x ∩ y) ↔ z ∈ x ∧ z ∈ y := by
  unfold inter
  intro z
  rw [separation_ax]

def subset (x y : Set) : Prop := ∀ z, z ∈ x → z ∈ y
infix:50 " ⊆ " => subset

axiom power_set : ∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x
noncomputable def power (x : Set) : Set := (power_set x).choose
theorem power_ax (x : Set) : ∀ z, z ∈ (power x) ↔ z ⊆ x := (power_set x).choose_spec

theorem subset_trans : ∀ x y z, x ⊆ y → y ⊆ z → x ⊆ z := by
  intro x y z
  intro h1 h2 u
  have h3 := h1 u
  have h4 := h2 u
  intro h5
  exact h4 (h3 h5)

theorem power_set_mono : ∀ x y, x ⊆ y → (power x) ⊆ (power y) := by
  intro x y
  intro h
  intro z
  rw [power_ax, power_ax]
  intro h2
  exact ((subset_trans z x y) h2) h
