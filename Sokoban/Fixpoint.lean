/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs

namespace Sokoban

/-- Subset relation on lists of positions. -/
def SubPos (xs ys : List Pos) : Prop :=
  ∀ x ∈ xs, x ∈ ys

theorem SubPos.refl (xs : List Pos) : SubPos xs xs :=
  fun _ h => h

theorem SubPos.trans {xs ys zs : List Pos} (h₁ : SubPos xs ys) (h₂ : SubPos ys zs) :
    SubPos xs zs :=
  fun x hx => h₂ x (h₁ x hx)

theorem nodup_filter {α : Type} {p : α → Bool} {xs : List α} (h : xs.Nodup) :
    (xs.filter p).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.nodup_cons] at h
    rcases h with ⟨ha, has⟩
    simp only [List.filter]
    split
    · simp only [List.nodup_cons]
      refine ⟨?_, ih has⟩
      intro hmem
      exact ha (List.mem_filter.mp hmem).1
    · exact ih has

/-- Simple duplicate-removal preserving membership, with trivial `Nodup` proof. -/
def dedupPos : List Pos → List Pos
  | [] => []
  | x :: xs => if xs.contains x then dedupPos xs else x :: dedupPos xs

theorem mem_dedupPos {x : Pos} {xs : List Pos} : x ∈ dedupPos xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [dedupPos]
  | cons a as ih =>
    simp only [dedupPos]
    cases hc : as.contains a
    · simp [ih]
    · simp only [↓reduceIte, ih, List.mem_cons]
      constructor
      · intro h; exact .inr h
      · rintro (rfl | h)
        · exact List.contains_iff_mem.mp hc
        · exact h

theorem nodup_dedupPos (xs : List Pos) : (dedupPos xs).Nodup := by
  induction xs with
  | nil => simp [dedupPos]
  | cons a as ih =>
    simp only [dedupPos]
    cases hc : as.contains a
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      rw [mem_dedupPos] at hmem
      have : as.contains a = true := List.contains_iff_mem.mpr hmem
      simp_all
    · exact ih

theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] {xs ys : List α}
    (hn : xs.Nodup) (hs : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a as ih =>
    simp only [List.nodup_cons] at hn
    rcases hn with ⟨ha, has⟩
    have ha_ys : a ∈ ys := hs a (by simp)
    have hsub : ∀ x ∈ as, x ∈ ys.erase a := by
      intro x hx
      have hx_ys : x ∈ ys := hs x (by simp [hx])
      have hne : x ≠ a := fun heq => ha (heq ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr hx_ys
    have hle := ih has hsub
    have herase := List.length_erase_of_mem ha_ys
    have hpos := List.length_pos_of_mem ha_ys
    simp only [List.length_cons]
    omega

theorem eq_mem_of_nodup_subset_length_eq {α : Type} [DecidableEq α] {xs ys : List α}
    (hnx : xs.Nodup) (_hny : ys.Nodup) (hs : ∀ x ∈ xs, x ∈ ys) (hl : xs.length = ys.length) :
    ∀ x, x ∈ xs ↔ x ∈ ys := by
  intro x
  constructor
  · exact hs x
  · intro hxy
    by_cases hnx_mem : x ∈ xs
    · exact hnx_mem
    · have hsub : ∀ z ∈ xs, z ∈ ys.erase x := by
        intro z hz
        have hzy : z ∈ ys := hs z hz
        have hne : z ≠ x := fun heq => hnx_mem (heq ▸ hz)
        exact (List.mem_erase_of_ne hne).mpr hzy
      have hle := length_le_of_nodup_subset hnx hsub
      have hlen := List.length_erase_of_mem hxy
      have hpos := List.length_pos_of_mem hxy
      omega

/-- Upward fixpoint iteration with early exit when length stops growing. -/
def iterFixedUp (f : List Pos → List Pos) : Nat → List Pos → List Pos
  | 0, xs => xs
  | n + 1, xs =>
    let xs' := f xs
    if xs'.length == xs.length then xs else iterFixedUp f n xs'

theorem iterFixedUp_subset_start {f : List Pos → List Pos} {bound : List Pos}
    (hf : ∀ ys, SubPos ys bound → SubPos ys (f ys) ∧ SubPos (f ys) bound) :
    ∀ fuel xs, SubPos xs bound → SubPos xs (iterFixedUp f fuel xs) := by
  intro fuel
  induction fuel with
  | zero => intro xs _; exact SubPos.refl xs
  | succ n ih =>
    intro xs hxb
    simp only [iterFixedUp]
    split
    · exact SubPos.refl xs
    · have h1 := (hf xs hxb).1
      have h2 := (hf xs hxb).2
      exact SubPos.trans h1 (ih (f xs) h2)

theorem iterFixedUp_subset_bound {f : List Pos → List Pos} {bound : List Pos}
    (hf : ∀ ys, SubPos ys bound → SubPos ys (f ys) ∧ SubPos (f ys) bound) :
    ∀ fuel xs, SubPos xs bound → SubPos (iterFixedUp f fuel xs) bound := by
  intro fuel
  induction fuel with
  | zero => intro xs hxb; exact hxb
  | succ n ih =>
    intro xs hxb
    simp only [iterFixedUp]
    split
    · exact hxb
    · exact ih (f xs) (hf xs hxb).2

theorem iterFixedUp_fixpoint {f : List Pos → List Pos} {bound : List Pos}
    (hbn : bound.Nodup)
    (hf : ∀ ys, SubPos ys bound → ys.Nodup →
      SubPos ys (f ys) ∧ SubPos (f ys) bound ∧ (f ys).Nodup) :
    ∀ fuel xs, SubPos xs bound → xs.Nodup → bound.length ≤ xs.length + fuel →
      ∀ x, x ∈ f (iterFixedUp f fuel xs) ↔ x ∈ iterFixedUp f fuel xs := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs hxb hxn hlen
    have hle : xs.length ≤ bound.length := length_le_of_nodup_subset hxn hxb
    have heq : xs.length = bound.length := by omega
    have hfull := eq_mem_of_nodup_subset_length_eq hxn hbn hxb heq
    have hfx := hf xs hxb hxn
    intro x
    constructor
    · intro hfx_mem
      exact (hfull x).mpr (hfx.2.1 x hfx_mem)
    · intro hx
      exact hfx.1 x hx
  | succ n ih =>
    intro xs hxb hxn hlen
    simp only [iterFixedUp]
    split
    · rename_i hbeq
      have hlen_eq : (f xs).length = xs.length := by
        simpa using hbeq
      have hfx := hf xs hxb hxn
      exact fun x => (eq_mem_of_nodup_subset_length_eq hxn hfx.2.2 hfx.1 hlen_eq.symm x).symm
    · rename_i hne
      have hneq : (f xs).length ≠ xs.length := by
        simpa using hne
      have hfx := hf xs hxb hxn
      have hle : xs.length ≤ (f xs).length := length_le_of_nodup_subset hxn hfx.1
      have hlt : xs.length + 1 ≤ (f xs).length := by omega
      exact ih (f xs) hfx.2.1 hfx.2.2 (by omega)

/-- Downward fixpoint iteration with early exit when length stops shrinking. -/
def iterFixedDown (f : List Pos → List Pos) : Nat → List Pos → List Pos
  | 0, xs => xs
  | n + 1, xs =>
    let xs' := f xs
    if xs'.length == xs.length then xs else iterFixedDown f n xs'

theorem iterFixedDown_subset {f : List Pos → List Pos}
    (hf : ∀ ys, ys.Nodup → SubPos (f ys) ys ∧ (f ys).Nodup) :
    ∀ fuel xs, xs.Nodup → SubPos (iterFixedDown f fuel xs) xs := by
  intro fuel
  induction fuel with
  | zero => intro xs _; exact SubPos.refl xs
  | succ n ih =>
    intro xs hxn
    simp only [iterFixedDown]
    split
    · exact SubPos.refl xs
    · have h := hf xs hxn
      exact SubPos.trans (ih (f xs) h.2) h.1

theorem iterFixedDown_nodup {f : List Pos → List Pos}
    (hf : ∀ ys, ys.Nodup → SubPos (f ys) ys ∧ (f ys).Nodup) :
    ∀ fuel xs, xs.Nodup → (iterFixedDown f fuel xs).Nodup := by
  intro fuel
  induction fuel with
  | zero => intro xs hxn; exact hxn
  | succ n ih =>
    intro xs hxn
    simp only [iterFixedDown]
    split
    · exact hxn
    · exact ih (f xs) (hf xs hxn).2

theorem iterFixedDown_fixpoint {f : List Pos → List Pos}
    (hf : ∀ ys, ys.Nodup → SubPos (f ys) ys ∧ (f ys).Nodup) :
    ∀ fuel xs, xs.Nodup → xs.length ≤ fuel →
      ∀ x, x ∈ f (iterFixedDown f fuel xs) ↔ x ∈ iterFixedDown f fuel xs := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs hxn hlen
    cases xs with
    | nil =>
      have h := hf [] (by simp)
      intro x
      constructor
      · intro hfx; exact h.1 x hfx
      · intro hx; cases hx
    | cons _ _ =>
      simp only [List.length_cons] at hlen
      omega
  | succ n ih =>
    intro xs hxn hlen
    simp only [iterFixedDown]
    split
    · rename_i hbeq
      have hlen_eq : (f xs).length = xs.length := by
        simpa using hbeq
      have h := hf xs hxn
      exact eq_mem_of_nodup_subset_length_eq h.2 hxn h.1 hlen_eq
    · rename_i hne
      have hneq : (f xs).length ≠ xs.length := by
        simpa using hne
      have h := hf xs hxn
      have hle : (f xs).length ≤ xs.length := length_le_of_nodup_subset h.2 h.1
      have hlt : (f xs).length ≤ n := by omega
      exact ih (f xs) h.2 hlt

end Sokoban
