/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k,hk⟩ := h
    use k
    addarith [hk]



theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    addarith [hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h1 : (x + 3 ) * ( x - 2) = 0 := by
      calc
      (x + 3 ) * ( x - 2) = x ^ 2 + x - 6 := by ring
                         _= 0 := by rw[h]
    have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
    obtain ha | hb := h2
    left
    addarith [ha]
    right
    addarith [hb]
  · intro h
    obtain h1 | h2 := h
    calc
      x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw [h1]
      _= 0 := by numbers
    calc
      x ^ 2 + x - 6 = (2) ^ 2 + (2) - 6 := by rw [h2]
      _= 0 := by numbers
#check abs_le_of_sq_le_sq'

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
constructor
· intro h
  have h1 : 2 * a - 5  ≥ - 1 ∧ 2 * a - 5 ≤ 1 := by
    apply abs_le_of_sq_le_sq'
    calc
      (2 * a - 5 ) ^ 2 = 4 * (a ^ 2 - 5 * a + 5 ) + 5 := by ring
                    _≤ 4 * -1 + 5 := by rel [h]
                    _= 1 ^ 2 := by numbers
    numbers
  obtain ⟨hp1, hp2⟩ := h1
  have h2 : 2 * a ≥ 2 * 2 ∧  2 * a ≤ 2 * 3 := by
    constructor
    · addarith [hp1]
    · addarith [hp2]
  obtain ⟨hq1,hq2⟩ := h2
  cancel 2 at hq1
  cancel 2 at hq2
  interval_cases a
  left
  numbers
  right
  numbers
· intro h
  obtain h1|h2 := h
  calc
  a ^ 2 - 5 * a + 5 = (2) ^ 2 - 5 * (2) + 5 := by rw[h1]
                     _≤ -1 := by numbers
  calc
  a ^ 2 - 5 * a + 5 = (3) ^ 2 - 5 * (3) + 5 := by rw[h2]
                     _≤ -1 := by numbers


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain h1 | h2 := hn2
  use 2
  have : n = 2 * 2  := by addarith [h1]
  apply this
  use 3
  have : n = 2 * 3  := by addarith [h2]
  apply this

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain h1 | h2 := hn1
  have : n = 4 := by addarith [h1]
  use 2
  addarith [this]
  have : n = 6 := by addarith [h2]
  use 3
  addarith [this]


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    have : x = 6 := by
      calc
      x = ( 2 * x - 1 + 1) / 2 := by ring
       _= (11 + 1 ) / 2 := by rw[h]
       _= 6 := by ring
    apply this
  · intro h
    calc
      2 * x - 1 = 2 * 6 - 1 := by rw[h]
               _= 11 := by numbers

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h
    constructor
    use 9 * k
    calc
      n = 63 * k := by rw[hk]
       _= 7 * ( 9 * k) := by ring
    use 7 * k
    calc
      n = 63 * k := by rw[hk]
       _= 9 * ( 7 * k) := by ring
  · intro h
    obtain ⟨hn1,hn2⟩:= h
    obtain ⟨j,hj⟩:= hn1
    obtain ⟨k,hk⟩:= hn2
    use ( 4 * k -3 *j )
    calc
      n = 4 * 7 * n + (-3 ) * 9 * n := by ring
      _= 4 * 7 * (9 * k) + (-3 ) * 9 * n := by rw[hk]
       _= 4 * 7 * (9 * k) + (-3 ) * 9 * (7 * j) := by rw[hj]
       _=63 * ( 4 * k -3 *j ) := by ring

theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    addarith [hk]
  · intro h
    obtain ⟨k,hk⟩:= h
    use k
    addarith [hk]

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
sorry
#check dvd_iff_modEq

#check abs_le_of_sq_le_sq'

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
constructor
· intro h
  have h' : k ≤ 2 := by
    sorry

· intro h
  obtain h1 | h2 | h3 := h
  calc
  k ^ 2 = 0 ^ 2 := by rw[h1]
       _≤ 6 := by numbers
  calc
  k ^ 2 = 1 ^ 2 := by rw[h2]
       _≤ 6 := by numbers
  calc
  k ^ 2 = 2 ^ 2 := by rw[h3]
       _≤ 6 := by numbers
