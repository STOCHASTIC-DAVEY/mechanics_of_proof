/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 :=
  calc
    m + 3 ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith[h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by addarith[h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h3,h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 :=
  calc t * t = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 :=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h1 : x ≤ -1 := by addarith[hx]
  have h2 : y ≥ 3- 2 * x := by addarith[hy,hx]
  calc y ≥ 3- 2 * x := by rel[h2]
        _≥ 3- 2 * (-1) := by rel[h1]
        _= 5 := by ring
        _> 3 := by numbers


example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : a + b ≥ 0 := by addarith[h1]
  have h4 : b - a ≥ 0 := by addarith[h2]
  calc
    a ^ 2 = a ^ 2 + 0 := by ring
         _=  a ^ 2 + 0 * (a + b) := by ring
         _≤  a ^ 2 + ( b - a ) * (a + b) := by rel[h3,h4]
         _= b ^ 2 := by ring


example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have hm : b - a ≥ 0 := by addarith[h]
  calc a ^ 3 = a ^ 3 + 0 := by ring
            _= a ^ 3 + 0 * 0 := by ring
            _= a ^ 3 + 0 * (( (b - a) ^ 2 + 3 * ( b + a ) ^ 2)/4 ) := by ring
            _≤ a ^ 3 + (b - a) * (( (b - a) ^ 2 + 3 * ( b + a ) ^ 2)/4 ):= by rel[hm]
            _= b ^ 3 := by ring

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
have h4 : x * (x + 2) = 2 * (x + 2) := by
  calc x * (x + 2) = x ^ 2 + 2 * x := by ring
                  _= 4 + 2 * x := by rw[h1]
                  _= 2 * (x + 2) := by ring
cancel (x + 2) at h4

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
have h2 : ( n - 2 ) ^ 2 = 0 := by
    calc ( n - 2 ) ^ 2 = (n ^ 2 + 4 ) - 4 * n := by ring
                      _= 4 * n - 4 * n := by rw[hn]
                      _= 0 := by ring
cancel 2 at h2
addarith [h2]

example (x y : ℚ) (h1 : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
have h3 : x * (1 -  y) ≥ 0 := by
  calc x * (1 -  y) = x - x * y := by ring
                _= x - 1 := by rw[h1]
                _≥ 1 - 1 := by rel [h2]
                _= 0 := by numbers
cancel x at h3
addarith [h3]
