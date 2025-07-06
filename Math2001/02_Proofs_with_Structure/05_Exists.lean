/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

#check le_or_gt
#check cancel

example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < x * ( - t ) := by
      calc
        0 < ( -x ) * t := by addarith [hxt]
         _= x * ( -t ) := by ring
    cancel x at hxt'
    have hxt'' :  t < 0 := by
      calc
        0 = t + (- t) := by ring
         _> t + 0 := by rel[hxt']
         _= t := by ring
    apply ne_of_lt
    apply hxt''


example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/ 2
  constructor
  · calc
      p = p / 2 + p / 2:= by ring
       _< p / 2 + q / 2 := by rel[h]
       _= (p + q) / 2 := by ring
  · calc
      (p + q) / 2 < (q + q) / 2 := by rel[h]
                 _= q := by ring

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt x 0
  obtain h1 | h2 := H
  · use 0.5
    calc 0.5 ^ 2 > 0 := by numbers
              _≥ x := by rel[h1]
  · use x + 1
    calc ( x + 1 ) ^ 2 = x ^ 2 + x + x + 1 := by ring
    _≥ 0 + x + x + 1 := by extra
    _= x + x + 1 := by ring
    _> 0 + x + 1 := by rel[h2]
    _= x + 1 := by ring
    _> x := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, hat⟩ := h
  have hx : ( 1 - a ) * ( t - 1 ) > 0 := by
    calc
      ( 1 - a ) * ( t - 1 ) = a + t - (1 + a * t) := by ring
                           _> a * t + 1 - (1 + a * t) := by rel[hat]
                           _= 0 := by ring
  have H := le_or_gt a 1
  obtain ( h1 | h2 ):= H
  · apply ne_of_gt
    have ha1 : 1 - a ≥ 0 := by addarith [h1]
    cancel 1 - a at hx
    addarith [hx]
  · apply ne_of_lt
    have ha2 : a-1 > 0 := by addarith [h2]
    have hx' : ( a - 1 ) * ( 1 - t ) > 0 := by
      calc
        ( a - 1 ) * ( 1 - t ) = ( 1 - a ) * ( t - 1 ) := by ring
                           _> 0 := by rel[hx]
    cancel a-1 at hx'
    addarith[hx']

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
