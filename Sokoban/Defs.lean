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

/-- Executable duplicate-free check on position lists. -/
def isNodupPos : List Pos → Bool
  | [] => true
  | x :: xs => !xs.contains x && isNodupPos xs

theorem isNodupPos_sound {xs : List Pos} (h : isNodupPos xs = true) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [isNodupPos, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hmem
    have : as.contains a = true := List.contains_iff_mem.mpr hmem
    simp_all

/-- State validity invariant: player and boxes are off walls, player is not on a box, and boxes are distinct. -/
def ValidState (L : Level) (s : State) : Prop :=
  L.isWall s.player = false ∧ s.player ∉ s.boxes ∧
  (∀ b ∈ s.boxes, L.isWall b = false) ∧ s.boxes.Nodup

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

theorem moveBox_nodup {bs : List Pos} {b b' : Pos}
    (hnd : bs.Nodup) (hnb : b' ∉ bs) : (moveBox bs b b').Nodup := by
  induction bs with
  | nil => simp [moveBox]
  | cons a as ih =>
    simp only [List.nodup_cons] at hnd
    have hnb_a : b' ≠ a := fun heq => hnb (heq ▸ by simp)
    have hnb_as : b' ∉ as := fun hm => hnb (by simp [hm])
    simp only [moveBox, List.map_cons, List.nodup_cons]
    by_cases hab : a = b
    · subst hab
      simp only [beq_self_eq_true, ↓reduceIte]
      refine ⟨?_, ih hnd.2 hnb_as⟩
      intro hmem
      simp only [List.mem_map] at hmem
      rcases hmem with ⟨y, hy, hy_eq⟩
      have hne : y ≠ a := fun heq => hnd.1 (heq ▸ hy)
      have hbeq : (y == a) = false := beq_false_of_ne hne
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hy_eq
      exact hnb_as (hy_eq ▸ hy)
    · have hbeq : (a == b) = false := beq_false_of_ne hab
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ih hnd.2 hnb_as⟩
      intro hmem
      simp only [List.mem_map] at hmem
      rcases hmem with ⟨y, hy, hy_eq⟩
      by_cases hyb : y = b
      · subst hyb
        simp only [beq_self_eq_true, ↓reduceIte] at hy_eq
        exact hnb_a hy_eq
      · have hbeqy : (y == b) = false := beq_false_of_ne hyb
        simp only [hbeqy, Bool.false_eq_true, ↓reduceIte] at hy_eq
        exact hnd.1 (hy_eq ▸ hy)

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
  rcases hv with ⟨hwp, hpb, hwb, hnd⟩
  cases hs with
  | walk d s hw hb =>
    exact ⟨hw, hb, hwb, hnd⟩
  | push d s hb hw hnb =>
    refine ⟨hwb _ hb, ?_, ?_, moveBox_nodup hnd hnb⟩
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
    have hwp : L.isWall (step s.player d) = false := hv.2.2.1 _ hb
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

/-- Boolean validity check for concrete states (including duplicate-free boxes). -/
def isValidStateBool (L : Level) (s : State) : Bool :=
  !L.isWall s.player && !s.boxes.contains s.player &&
  s.boxes.all (fun b => !L.isWall b) && isNodupPos s.boxes

theorem isValidStateBool_sound {L : Level} {s : State} (h : isValidStateBool L s = true) :
    ValidState L s := by
  simp only [isValidStateBool, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  rcases h with ⟨⟨⟨hw, hpb⟩, hwb⟩, hnd⟩
  refine ⟨hw, ?_, hwb, isNodupPos_sound hnd⟩
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

private def isValidXsbChar (c : Char) : Bool :=
  c == '#' || c == '@' || c == '+' || c == '$' || c == '*' || c == '.' || c == ' '

/--
Strict XSB board parser rejecting empty grids, unknown characters, missing/multiple players,
zero boxes, and mismatched box/goal counts.
-/
def parseLevelStrict (rows : List String) : Option (Level × State × List Pos) :=
  if rows.isEmpty then none
  else
    let chars := rows.foldl (fun acc r => acc ++ r.toList) []
    if !chars.all isValidXsbChar then none
    else
      let players := (chars.filter (fun c => c == '@' || c == '+')).length
      let boxes := (chars.filter (fun c => c == '$' || c == '*')).length
      let goals := (chars.filter (fun c => c == '.' || c == '+' || c == '*')).length
      if players == 1 && boxes >= 1 && boxes == goals then
        some (parseLevel rows)
      else
        none

end Parser

end Sokoban
