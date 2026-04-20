axiom Set : Type

axiom Elem : Set → Set → Prop
infix:50 " ∈ " => Elem
def nin (x y : Set) : Prop := ¬ (x ∈ y)
infix:50 " ∉ " => nin

axiom extensionality : ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y

axiom empty_set : ∃ x, ∀ y, y ∉ x
noncomputable def empty : Set := empty_set.choose
theorem empty_ax : ∀ y, y ∉ empty := empty_set.choose_spec

axiom pair_set : ∀ x y, ∃ z, ∀ u, u ∈ z ↔ u = x ∨ u = y
noncomputable def pair (x y : Set) : Set := (pair_set x y).choose
theorem pair_ax (x y : Set) : ∀ u, u ∈ (pair x y) ↔ u = x ∨ u = y := (pair_set x y).choose_spec

-- xは集合の集合、yは集合、zは元、uは集合と考えると覚えられるかも。
-- しかしあくまでも意味はないことに気をつける。
axiom union_set : ∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ u, z ∈ u ∧ u ∈ x
noncomputable def union (x : Set) : Set := (union_set x).choose
theorem union_ax (x : Set) : ∀ z, z ∈ (union x) ↔ ∃ u, z ∈ u ∧ u ∈ x := (union_set x).choose_spec

-- xの中で述語φを満たす要素だけからなる集合が存在する
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
theorem subset_trans : ∀ x y z, x ⊆ y → y ⊆ z → x ⊆ z := by
  intro x y z h1 h2 u h3
  exact (h2 u) ((h1 u) h3)

axiom power : ∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x
noncomputable def power_set (x : Set) : Set := (power x).choose
theorem power_ax (x : Set) : ∀ z, z ∈ (power_set x) ↔ z ⊆ x := (power x).choose_spec

axiom regularity : ∀ x, x ≠ empty → ∃ y, y ∈ x ∧ ((y ∩ x) = empty)

noncomputable def singleton' (x : Set) : Set := pair x x
theorem singleton_ax (x y : Set) : y ∈ singleton' x ↔ y = x := by
  unfold singleton'
  rw [pair_ax]
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact h
  · intro h
    exact Or.inl h
