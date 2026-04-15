class MyGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  -- x(yz) = (xy)z
  associative : ∀ x y z, mul x (mul y z) = mul (mul x y) z
  left_identity : ∀ x : G, mul one  x = x
  left_inverse : ∀ x : G, mul (inv x) x = one

open MyGroup in
theorem right_inverse {G : Type} [MyGroup G] (x : G) :
  mul x (inv x) = one := by
    calc mul x (inv x)
      -- e (x x^{-1})
      _ = mul one (mul x (inv x)) := by rw [left_identity]
      -- (e x) x^{-1}
      _ = mul (mul one x) (inv x) := by rw [associative]
      -- ((x^{-1}^{-1} x^{-1}) x) x^{-1}
      _ = mul (mul (mul (inv (inv x)) (inv x)) x) (inv x) := by rw [left_inverse]
      -- (x^{-1}^{-1} (x^{-1} x)) x^{-1} ... associative
      _ = mul (mul (inv (inv x)) (mul (inv x) x)) (inv x) := by rw [associative]
      -- (x^{-1}^{-1} e) x^{-1} ... left_inverse
      _ = mul (mul (inv (inv x)) one) (inv x) := by rw [left_inverse]
      -- x^{-1}^{-1} (e x^{-1}) ... associative
      _ = mul (inv (inv x)) (mul one (inv x)) := by rw [associative]
      -- x^{-1}^{-1} x^{-1} ... left_identity
      _ = mul (inv (inv x)) (inv x) := by rw [left_identity]
      -- e ... left_inverse
      _ = one := by rw [left_inverse]

open MyGroup in
theorem right_identity {G : Type} [MyGroup G] (x : G) :
  -- x e = x
  mul x one = x := by
    -- x e
    calc mul x one
      -- x (x^{-1} x) ... left_inverse
      _ = mul x (mul (inv x) x) := by rw [left_inverse]
      -- (x x^{-1}) x ... associative
      _ = mul (mul x (inv x)) x := by rw [associative]
      -- e x ... right_inverse
      _ = mul one x := by rw [right_inverse]
      -- x ... left_identity
      _ = x := by rw [left_identity]
