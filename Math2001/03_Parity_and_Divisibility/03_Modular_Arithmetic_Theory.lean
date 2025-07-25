/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init


example : 11 ≡ 3 [ZMOD 4] := by
  use 2
  numbers

example : -5 ≡ 1 [ZMOD 3] := by
  use -2
  numbers

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring


theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  obtain ⟨k,hk⟩:= h1
  obtain ⟨j,hj⟩:= h2
  use k -j
  calc
  ( a - c ) - ( b - d ) = (a-b)-(c-d) := by ring
                       _= n * k - n * j := by rw[hk,hj]
                       _= n * (k -j ) := by ring

theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
obtain ⟨k,hk⟩:= h1
use (-k)
calc
  - a - - b = - (a - b ) := by ring
           _= -(n * k) := by rw[hk]
           _= n * (-k) := by ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring


theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring


theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨k,hk⟩ := h
  use k * (a ^ 2 + a * b + b ^ 2)
  calc
    a ^ 3 - b ^ 3 = ( a - b ) * ( a ^ 2 + a * b + b ^ 2) := by ring
                 _= n * k * (a ^ 2 + a * b + b ^ 2) := by rw[hk]
                 _= n *( k * (a ^ 2 + a * b + b ^ 2)) := by ring

theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] :=
  sorry -- we'll prove this later in the book


theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := ha
  use x * (b ^ 2 + a * b + 2 * b + 3)
  calc
    a * b ^ 2 + a ^ 2 * b + 3 * a - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2) =
        (a - 2) * (b ^ 2 + a * b + 2 * b + 3) :=
      by ring
    _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
    _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.pow
  apply ha
  apply Int.ModEq.refl
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply ha

/-! # Exercises -/


example : 34 ≡ 104 [ZMOD 5] := by
  use -14
  numbers

theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
obtain ⟨k,hk⟩:= h
use -k
calc
  b - a = - ( a - b ) := by ring
       _= - (n * k) := by rw[hk]
       _= n * -k := by ring

theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
obtain ⟨ k, hk⟩ := h1
obtain ⟨ j, hj⟩ := h2
use k + j
calc
a - c = (a-b)+(b-c) := by ring
     _= n * k + n * j := by rw[hk,hj]
     _= n * (k + j):= by ring

example : a + n * c ≡ a [ZMOD n] := by
use c
ring


example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
obtain ⟨k,hk⟩:= h
use 2 * k
calc
  2 * a + 3 - (2 * b + 3) = 2 * (a-b) := by ring
                         _= 2 * (5 * k) := by rw[hk]
                         _= 5 * (2 * k) := by ring


example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
obtain ⟨k,hk⟩:=h
use 3 * k
calc
  3 * m -1 - (3 * n -1) = 3 * (m - n) := by ring
                    _= 3 * (4 * k ) := by rw[hk]
                    _= 4 * (3 * k) := by ring


example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
obtain ⟨a, ha⟩:= hb
use ( 4 * a + a * ( k ^ 2 + 3 * k + 9))
calc
  4 * k + k ^ 3 + 3 - ( 4 * 3 + 3 ^ 3 + 3) = 4 * ( k - 3) + (k ^ 3 - 3 ^ 3) := by ring
  _= 4 * ( k - 3) + (k - 3 ) * ( k ^ 2 + 3 * k + 9) := by ring
  _= 4 * (5 * a) + (5 * a) * ( k ^ 2 + 3 * k + 9) := by rw[ha]
  _= 5 * ( 4 * a + a * ( k ^ 2 + 3 * k + 9)) := by ring
