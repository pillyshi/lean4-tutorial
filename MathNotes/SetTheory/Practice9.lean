axiom Set : Type

axiom Elem : Set → Set → Prop
infix:50 " ∈ " => Elem
noncomputable def notin (x y : Set) : Prop := ¬ (x ∈ y)
infix:50 " ∉ " => notin

axiom extensionality : ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y

axiom empty_set : ∃ x, ∀ y, y ∉ x
noncomputable def empty : Set := empty_set.choose
theorem empty_ax : ∀ y, y ∉ empty := empty_set.choose_spec

axiom pair_set : ∀ x y, ∃ z, ∀ u, u ∈ z ↔ u = x ∨ u = y
noncomputable def pair (x y : Set) : Set := (pair_set x y).choose
theorem pair_ax (x y : Set) : ∀ u, u ∈ (pair x y) ↔ u = x ∨ u = y := (pair_set x y).choose_spec

axiom union_set : ∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ u, z ∈ u ∧ u ∈ x
noncomputable def union (x : Set) : Set := (union_set x).choose
theorem union_ax (x : Set) : ∀ z, z ∈ (union x) ↔ ∃ u, z ∈ u ∧ u ∈ x := (union_set x).choose_spec
noncomputable def binary_union (x y : Set) : Set := union (pair x y)
infix:50 " ∪ " => binary_union
theorem binary_union_def : ∀ x y, ∀ z, z ∈ (x ∪ y) ↔ z ∈ x ∨ z ∈ y := by
  intro x y z
  unfold binary_union
  rw [union_ax]
  constructor
  · intro h
    obtain ⟨u, h2⟩ := h
    obtain ⟨h3, h4⟩ := h2
    have h5 := (pair_ax x y u).mp h4
    cases h5 with
    | inl h5 => exact Or.inl (h5 ▸ h3)
    | inr h5 => exact Or.inr (h5 ▸ h3)
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
noncomputable def inter (x y : Set) : Set := (separation x (fun z => z ∈ y))
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

axiom regularity_set : ∀ x, x ≠ empty → ∃ y, y ∈ x ∧ ((x ∩ y) = empty)

--

noncomputable def singleton' (x : Set) : Set := pair x x
theorem singleton_ax : ∀ x y, y ∈ (singleton' x) ↔ y = x := by
  unfold singleton'
  intro x y
  rw [pair_ax]
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact h
  · intro h
    exact Or.inl h

-- theorems

theorem empty_unique : ∀ e e', (∀ x, x ∉ e) → (∀ x, x ∉ e') → e = e' := by
  intro e e' h1 h2
  apply extensionality
  intro z
  constructor
  · intro h3
    exact absurd h3 (h1 z)
  · intro h3
    exact absurd h3 (h2 z)

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
  intro x y z
  unfold subset
  intro h1 h2 u h3
  exact (h2 u) ((h1 u) h3)

theorem empty_subset : ∀ x, empty ⊆ x := by
  intro x
  unfold subset
  intro y h
  exact absurd h (empty_ax y)

theorem union_empty : ∀ x, (x ∪ empty) = x := by
  intro x
  unfold binary_union
  apply extensionality
  intro y
  rw [union_ax]
  constructor
  · intro h
    obtain ⟨z, h2⟩ := h
    obtain ⟨h3, h4⟩ := h2
    have h5 := (pair_ax x empty z).mp h4
    cases h5 with
    | inl h5 => exact h5 ▸ h3
    | inr h5 => exact absurd (h5 ▸ h3) (empty_ax y)
  · intro h
    exists x
    exact ⟨h, (pair_ax x empty x).mpr (Or.inl rfl)⟩

theorem power_set_mono : ∀ x y, x ⊆ y → (power x) ⊆ (power y) := by
  intro x y h z
  rw [power_ax, power_ax]
  intro h2
  exact ((subset_trans z x y) h2) h

theorem no_self_membership : ∀ x, x ∉ x := by
  intro x h
  have h2 := (singleton_ax x x).mpr rfl
  have h3 : (singleton' x) ≠ empty := by
    intro h4
    exact (h4 ▸ empty_ax x) h2
  have h5 := (regularity_set (singleton' x)) h3
  obtain ⟨y, h6⟩ := h5
  obtain ⟨h7, h8⟩ := h6
  have h9 := (singleton_ax x y).mp h7
  have h10 := (h9 ▸ h8) ▸ (empty_ax x)
  have h11 := (inter_def (singleton' x) x x).mpr ⟨h2, h⟩
  exact h10 h11
