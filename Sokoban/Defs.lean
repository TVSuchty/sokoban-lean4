/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/

namespace Sokoban

/-- Cardinal movement directions on the Sokoban grid. -/
inductive Dir where
  | up | down | left | right
  deriving DecidableEq, Repr, BEq

namespace Dir

/-- Opposite direction (180-degree reversal). -/
def opp : Dir → Dir
  | up => down
  | down => up
  | left => right
  | right => left

theorem opp_opp (d : Dir) : d.opp.opp = d := by
  cases d <;> rfl

/-- All four cardinal directions in fixed order. -/
def all : List Dir := [.up, .down, .left, .right]

theorem mem_all (d : Dir) : d ∈ all := by
  cases d <;> simp [all]

end Dir

/-- Grid coordinates `(x, y)` with `x` increasing right and `y` increasing down. -/
abbrev Pos := Int × Int

/-- Move one cell in direction `d`. -/
def step (p : Pos) : Dir → Pos
  | .up => (p.1, p.2 - 1)
  | .down => (p.1, p.2 + 1)
  | .left => (p.1 - 1, p.2)
  | .right => (p.1 + 1, p.2)

theorem step_opp (p : Pos) (d : Dir) : step (step p d) d.opp = p := by
  cases d <;> simp [step, Dir.opp] <;> omega

theorem step_ne (p : Pos) (d : Dir) : step p d ≠ p := by
  intro h
  rcases p with ⟨x, y⟩
  cases d <;> simp [step] at h <;> omega

/-- Static geometry of a Sokoban level: walls and goal squares. -/
structure Level where
  isWall : Pos → Bool
  isGoal : Pos → Bool

/-- Dynamic game state: player coordinate and list of box coordinates. -/
structure State where
  player : Pos
  boxes : List Pos
  deriving DecidableEq, Repr, BEq

/-- State validity invariant: player and boxes are off walls, and player is not on a box. -/
def ValidState (L : Level) (s : State) : Prop :=
  L.isWall s.player = false ∧ s.player ∉ s.boxes ∧ ∀ b ∈ s.boxes, L.isWall b = false

/-- Replace box coordinate `b` with `b'` in `bs`. -/
def moveBox (bs : List Pos) (b b' : Pos) : List Pos :=
  bs.map (fun x => if x == b then b' else x)

theorem mem_moveBox {bs : List Pos} {b b' x : Pos} (hb : b ∈ bs) :
    x ∈ moveBox bs b b' ↔ x = b' ∨ (x ∈ bs ∧ x ≠ b) := by
  simp only [moveBox, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hyb : y = b
    · subst hyb
      simp
    · right
      have hbeq : (y == b) = false := beq_false_of_ne hyb
      simp [hbeq, hy, hyb]
  · rintro (rfl | ⟨hx, hne⟩)
    · refine ⟨b, hb, by simp⟩
    · refine ⟨x, hx, ?_⟩
      have hbeq : (x == b) = false := beq_false_of_ne hne
      simp [hbeq]

theorem moveBox_not_mem_old {bs : List Pos} {b b' : Pos} (hne : b ≠ b') :
    b ∉ moveBox bs b b' := by
  simp only [moveBox, List.mem_map, not_exists, not_and]
  intro y _ hy
  by_cases hyb : y = b
  · subst hyb
    simp at hy
    exact hne hy.symm
  · have hbeq : (y == b) = false := beq_false_of_ne hyb
    simp [hbeq] at hy
    exact hyb hy

/-- Single legal Sokoban transition (walk or push). -/
inductive Step (L : Level) : State → State → Prop where
  | walk (d : Dir) (s : State)
      (hw : L.isWall (step s.player d) = false)
      (hb : step s.player d ∉ s.boxes) :
      Step L s { player := step s.player d, boxes := s.boxes }
  | push (d : Dir) (s : State)
      (hb : step s.player d ∈ s.boxes)
      (hw : L.isWall (step (step s.player d) d) = false)
      (hnb : step (step s.player d) d ∉ s.boxes) :
      Step L s
        { player := step s.player d
          boxes := moveBox s.boxes (step s.player d) (step (step s.player d) d) }

theorem Step.preserves_valid {L : Level} {s₁ s₂ : State}
    (hv : ValidState L s₁) (hs : Step L s₁ s₂) : ValidState L s₂ := by
  rcases hv with ⟨hwp, hpb, hwb⟩
  cases hs with
  | walk d s hw hb =>
    exact ⟨hw, hb, hwb⟩
  | push d s hb hw hnb =>
    refine ⟨hwb _ hb, ?_, ?_⟩
    · exact moveBox_not_mem_old (step_ne _ d).symm
    · intro b hmem
      rw [mem_moveBox hb] at hmem
      rcases hmem with rfl | ⟨hb', _⟩
      · exact hw
      · exact hwb b hb'

/-- Multi-step reachability in Sokoban. -/
inductive Reach (L : Level) : State → State → Prop where
  | refl (s : State) : Reach L s s
  | step {s₁ s₂ s₃ : State} : Step L s₁ s₂ → Reach L s₂ s₃ → Reach L s₁ s₃

theorem Reach.single {L : Level} {s₁ s₂ : State} (h : Step L s₁ s₂) : Reach L s₁ s₂ :=
  Reach.step h (Reach.refl s₂)

theorem Reach.trans {L : Level} {s₁ s₂ s₃ : State}
    (h₁₂ : Reach L s₁ s₂) (h₂₃ : Reach L s₂ s₃) : Reach L s₁ s₃ := by
  induction h₁₂ with
  | refl => exact h₂₃
  | step hs _ ih => exact Reach.step hs (ih h₂₃)

theorem Reach.preserves_valid {L : Level} {s₁ s₂ : State}
    (hv : ValidState L s₁) (hr : Reach L s₁ s₂) : ValidState L s₂ := by
  induction hr with
  | refl => exact hv
  | step hs _ ih => exact ih (hs.preserves_valid hv)

/-- All boxes lie on goal squares. -/
def IsSolved (L : Level) (s : State) : Prop :=
  ∀ b ∈ s.boxes, L.isGoal b = true

/-- A state is solvable iff some solved state is reachable from it. -/
def Solvable (L : Level) (s : State) : Prop :=
  ∃ s', Reach L s s' ∧ IsSolved L s'

/-- A state is a deadlock iff it is unsolvable. -/
def IsDeadlock (L : Level) (s : State) : Prop :=
  ¬ Solvable L s

/-- Executable single-direction transition function. -/
def execDir (L : Level) (s : State) (d : Dir) : Option State :=
  let p' := step s.player d
  if L.isWall p' then none
  else if !s.boxes.contains p' then
    some { player := p', boxes := s.boxes }
  else
    let b' := step p' d
    if !L.isWall b' && !s.boxes.contains b' then
      some { player := p', boxes := moveBox s.boxes p' b' }
    else
      none

theorem execDir_sound {L : Level} {s s' : State} {d : Dir}
    (h : execDir L s d = some s') : Step L s s' := by
  simp only [execDir] at h
  cases hw : L.isWall (step s.player d)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
    cases hc1 : s.boxes.contains (step s.player d)
    · simp only [hc1, Bool.not_false, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine Step.walk d s hw ?_
      intro hm
      have hct := List.contains_iff_mem.mpr hm
      rw [hc1] at hct
      contradiction
    · simp only [hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hb : step s.player d ∈ s.boxes := List.contains_iff_mem.mp hc1
      cases hw2 : L.isWall (step (step s.player d) d)
      · cases hc2 : s.boxes.contains (step (step s.player d) d)
        · simp only [hw2, hc2, Bool.not_false, Bool.and_self, ↓reduceIte, Option.some.injEq] at h
          subst h
          refine Step.push d s hb hw2 ?_
          intro hm
          have hct := List.contains_iff_mem.mpr hm
          rw [hc2] at hct
          contradiction
        · simp only [hw2, hc2, Bool.not_false, Bool.not_true, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte] at h
          contradiction
      · simp only [hw2, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
        contradiction
  · simp only [hw, ↓reduceIte] at h
    contradiction

theorem step_implies_execDir {L : Level} {s s' : State}
    (hv : ValidState L s) (h : Step L s s') :
    ∃ d : Dir, execDir L s d = some s' := by
  cases h with
  | walk d s hw hb =>
    refine ⟨d, ?_⟩
    simp [execDir, hw, hb]
  | push d s hb hw hnb =>
    refine ⟨d, ?_⟩
    have hwp : L.isWall (step s.player d) = false := hv.2.2 _ hb
    simp [execDir, hwp, hb, hw, hnb]

/-- Execute a list of moves. -/
def applyMoves (L : Level) (s : State) : List Dir → Option State
  | [] => some s
  | d :: ds =>
    match execDir L s d with
    | none => none
    | some s' => applyMoves L s' ds

theorem applyMoves_sound {L : Level} {s s' : State} {ms : List Dir}
    (h : applyMoves L s ms = some s') : Reach L s s' := by
  induction ms generalizing s with
  | nil =>
    simp [applyMoves] at h
    subst h
    exact Reach.refl s
  | cons d ds ih =>
    simp only [applyMoves] at h
    cases hd : execDir L s d with
    | none => simp [hd] at h
    | some s₁ =>
      simp [hd] at h
      exact Reach.step (execDir_sound hd) (ih h)

/-- Boolean goal check. -/
def isSolvedBool (L : Level) (s : State) : Bool :=
  s.boxes.all L.isGoal

theorem isSolvedBool_sound {L : Level} {s : State} (h : isSolvedBool L s = true) :
    IsSolved L s := by
  simp only [isSolvedBool, List.all_eq_true] at h
  exact h

theorem solvable_of_applyMoves {L : Level} {s s' : State} {ms : List Dir}
    (hm : applyMoves L s ms = some s') (hs : isSolvedBool L s' = true) :
    Solvable L s :=
  ⟨s', applyMoves_sound hm, isSolvedBool_sound hs⟩

/-- Boolean validity check for concrete states. -/
def isValidStateBool (L : Level) (s : State) : Bool :=
  !L.isWall s.player && !s.boxes.contains s.player && s.boxes.all (fun b => !L.isWall b)

theorem isValidStateBool_sound {L : Level} {s : State} (h : isValidStateBool L s = true) :
    ValidState L s := by
  simp only [isValidStateBool, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  rcases h with ⟨⟨hw, hpb⟩, hwb⟩
  refine ⟨hw, ?_, hwb⟩
  intro hmem
  have : s.boxes.contains s.player = true := List.contains_iff_mem.mpr hmem
  simp_all

section Parser

private def getAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAt? xs n

private def gridChar (grid : List (List Char)) (p : Pos) : Char :=
  if p.1 < 0 || p.2 < 0 then '#'
  else
    match getAt? grid p.2.toNat with
    | none => '#'
    | some row => (getAt? row p.1.toNat).getD '#'

/--
Parse an ASCII XSB Sokoban board into `(level, initialState, playableSquares)`:
- `#` wall
- `@` player, `+` player on goal
- `$` box, `*` box on goal
- `.` empty goal, `' '` floor
Out-of-bounds coordinates default to `#` (wall).
-/
def parseLevel (rows : List String) : Level × State × List Pos :=
  let grid : List (List Char) := rows.map String.toList
  let L : Level :=
    { isWall := fun p => gridChar grid p == '#'
      isGoal := fun p =>
        let c := gridChar grid p
        c == '.' || c == '+' || c == '*' }
  let rec scanRow (y : Nat) (x : Nat) (cs : List Char)
      (player : Pos) (boxes playable : List Pos) : Pos × List Pos × List Pos :=
    match cs with
    | [] => (player, boxes, playable)
    | c :: rest =>
      let pos : Pos := (Int.ofNat x, Int.ofNat y)
      let player' := if c == '@' || c == '+' then pos else player
      let boxes' := if c == '$' || c == '*' then boxes ++ [pos] else boxes
      let playable' := if c != '#' then playable ++ [pos] else playable
      scanRow y (x + 1) rest player' boxes' playable'
  let rec scanRows (y : Nat) (gs : List (List Char))
      (player : Pos) (boxes playable : List Pos) : Pos × List Pos × List Pos :=
    match gs with
    | [] => (player, boxes, playable)
    | row :: rest =>
      let (p', b', pl') := scanRow y 0 row player boxes playable
      scanRows (y + 1) rest p' b' pl'
  let (player, boxes, playable) := scanRows 0 grid (0, 0) [] []
  (L, { player := player, boxes := boxes }, playable)

end Parser

end Sokoban
