/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
  7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw[hk]
           _= 2 * ( 7 * k + 1) + 1:= by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + 3 *b + a + 1
  calc
  x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw[ha,hb]
  _= 2 *(2 * a * b + 3 *b + a + 1) + 1 := by ring


example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc
    3 * m - 5 = 3 * (2 * t + 1 ) - 5 := by rw [ht]
             _= 2 * (3 * t - 1 ) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨t, ht⟩:= hn
  use 2 * t ^ 2 + 2 * t -3
  calc
    n ^ 2 + 2 * n - 5 = ( 2 * t ) ^ 2 + 2 * (2 * t) - 5:= by rw[ht]
                     _= 2 *( 2 * t ^ 2 + 2 * t - 3 ) + 1 := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨k, hk⟩:= hm
  obtain ⟨j, hj⟩:= hn
  use  k + j
  calc
  n + m = 2 * j + (2 * k + 1) := by rw[hk,hj]
  _= 2 * ( k + j ) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨k, hk⟩:= hp
  obtain ⟨j, hj⟩:= hq
  use k - j - 2
  calc
    p - q - 4 = 2 * k + 1 - (2 * j) - 4 := by rw[hk,hj]
    _= 2 * ( k - j - 2 ) + 1 := by ring


example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨k, hk⟩:= ha
  obtain ⟨j, hj⟩:= hb
  use 3 * k + j - 1
  calc
    3 * a + b - 3 = 3 * (2 * k) + ( 2 * j + 1 ) - 3 := by rw[hk,hj]
                 _= 2 * ( 3 * k + j - 1 ) := by ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨k, hk⟩:= hr
  obtain ⟨j, hj⟩:= hs
  use 3 * k - 5 * j - 1
  calc
    3 * r - 5 * s = 3 * (2 * k + 1) - 5 * (2 * j + 1 ) := by rw[hk,hj]
                 _= 2 * ( 3 * k - 5 * j - 1 ) := by ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hk⟩:= hx
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  calc
    x ^ 3 = ( 2 * k + 1 ) ^ 3 := by rw[hk]
         _= 8 * k ^ 3 + 12 * k ^ 2 + 6 * k + 1 := by ring
         _= 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hk⟩:= hn
  use (( 2 * k - 1 ) * k)
  calc
    n ^ 2 - 3 * n + 2 = ( n - 2 ) * (n - 1) := by ring
    _= ( 2 * k + 1 - 2 ) * (2 * k + 1 - 1) := by rw[hk]
    _= 2 * (( 2 * k - 1 ) * k) := by ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k,hk⟩:= ha
  use 2 * k ^ 2 + 4 * k - 1
  calc
  a ^ 2 + 2 * a - 4 = (2 * k + 1) ^ 2 + 2 * (2 * k + 1) - 4 := by rw[hk]
                   _= 4 * k ^ 2 + 4 * k + 1 + 4 * k + 2 - 4 := by ring
                   _= 2 * ( 2 * k ^ 2 + 4 * k - 1) + 1 := by ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k,hk⟩:= hp
  use 2 * k ^ 2 + 5 * k - 1
  calc
  p ^ 2 + 3 * p - 5 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw[hk]
                   _= 4 * k ^ 2 + 4 * k + 1 + 6 * k + 3 - 5 := by ring
                   _= 2 * ( 2 * k ^ 2 + 5 * k - 1 ) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨k,hk⟩:= hx
  obtain ⟨j,hj⟩:= hy
  use 2 * k * j + k + j
  calc
  x * y = ( 2 * k + 1 ) * ( 2 * j + 1) := by rw[hk,hj]
       _= 2 * ( 2 * k * j + k + j) + 1 := by ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain hn | hn := even_or_odd n
  · obtain ⟨k, hk⟩ := hn
    use 6 * k ^ 2 + 3 * k - 1
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hk]
      _ = 12 * k ^ 2 + 6 * k - 1 := by ring
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring
  · obtain ⟨k, hk⟩ := hn
    use 6 * k ^ 2 + 9 * k + 2
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hk]
      _ = 3 * (4 * k ^ 2 + 4 * k + 1) + 6 * k + 3 - 1 := by ring
      _ = 12 * k ^ 2 + 18 * k + 5 := by ring
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn | hn := even_or_odd n
  · obtain ⟨k, hk⟩ := hn
    use n + 1
    constructor
    extra
    use k
    calc
        n + 1 = (2 * k) + 1 := by rw[hk]
        _= 2 * k + 1:= by ring
  · obtain ⟨k, hk⟩ := hn
    use n
    constructor
    extra
    use k
    rw [hk]




example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
obtain ha | ha := even_or_odd a
· obtain hb | hb := even_or_odd b
  · obtain ⟨k,hk⟩ := ha
    obtain ⟨j,hj⟩ := hb
    left
    use k - j
    calc
      a - b = (2 * k) - (2 * j) := by addarith [hk,hj]
           _= 2 * ( k - j ) := by ring
  · obtain hc | hc := even_or_odd c
    · right
      left
      obtain ⟨k,hk⟩ := ha
      obtain ⟨j,hj⟩ := hc
      use k + j
      calc
      a + c = 2 * k + 2 * j := by rw[hk,hj]
           _= 2 * (k + j) := by ring
    · right
      right
      obtain ⟨k,hk⟩ := hb
      obtain ⟨j,hj⟩ := hc
      use k - j
      calc
      b - c = (2 * k + 1 ) - (2 * j + 1 ) := by rw[hk,hj]
           _= 2 * (k - j) := by ring
· obtain hb | hb := even_or_odd b
  · obtain hc | hc := even_or_odd c
    · right
      right
      obtain ⟨k,hk⟩ := hb
      obtain ⟨j,hj⟩ := hc
      use k - j
      calc
      b - c = (2 * k ) - (2 * j) := by rw[hk,hj]
         _= 2 * (k - j) := by ring
    · right
      left
      obtain ⟨k,hk⟩ := ha
      obtain ⟨j,hj⟩ := hc
      use k + j + 1
      calc
      a + c = (2 * k + 1 ) + (2 * j + 1) := by rw[hk,hj]
         _= 2 * (k + j + 1) := by ring
  · left
    obtain ⟨k,hk⟩ := ha
    obtain ⟨j,hj⟩ := hb
    use k - j
    calc a - b = 2 * k + 1 - ( 2 * j + 1) := by rw[hk,hj]
              _= 2 * (k - j) := by ring
