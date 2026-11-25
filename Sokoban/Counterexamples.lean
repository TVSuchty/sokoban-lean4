/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs
import Sokoban.DeadSquares
import Sokoban.Freeze

namespace Sokoban

/-!
# Formal Counterexamples to Tempting Unsound Sokoban Heuristics

A deadlock heuristic in a Sokoban solver MUST be **sound**: whenever it returns `true`,
the state must genuinely be unsolvable (`¬ Solvable L s`). A single false positive causes
the solver to prune a winning branch and falsely declare a solvable puzzle unsolvable.

Below we formalize three classic, intuitive heuristics that people often assume are sound,
and prove formally in Lean 4 that **all three are unsound** — while our verified
`isSuperFreezeDeadlock` correctly returns `false` on every one of them.
-/

-- ============================================================================
-- Heuristic 1: Treating a Simple Dead Square like a Wall on the Pushing Side
-- ============================================================================

/--
**Unsound Heuristic 1 (`naiveDeadSquareFreeze`):**
Marks a box `b` blocked in direction `d` if `step b d` is a wall, in `F`, **or** a Simple Dead Square,
OR if `step b d.opp` is a wall or in `F`.
Bug: To push `b` in direction `d`, the destination `step b d` must be live — but the *pushing side*
`step b d.opp` is allowed to be a dead square (the player can stand on a dead square to push)!
Checking both sides symmetrically (e.g. `dead(left) || dead(right)` instead of `wall(left) || wall(right) || (dead(left) && dead(right))`)
falsely flags boxes right next to a goal!
-/
def naiveDeadSquareDirBlocked (L : Level) (live F : List Pos) (b : Pos) (d : Dir) : Bool :=
  let dest := step b d
  let pushPos := step b d.opp
  L.isWall dest || F.contains dest || !live.contains dest ||
  L.isWall pushPos || F.contains pushPos || !live.contains pushPos

def naiveDeadSquareFreeze (L : Level) (playable : List Pos) (s : State) : Bool :=
  let live := computeLiveSquares L playable
  let stepFn (F : List Pos) : List Pos :=
    F.filter (fun b => Dir.all.all (naiveDeadSquareDirBlocked L live F b))
  let F := iterFixedDown stepFn s.boxes.length (dedupPos s.boxes)
  F.any (fun b => !L.isGoal b)

/-- Minimal 5×3 counterexample: `@` stands on a corner dead square `(1,1)` and pushes `$` right onto `.`. -/
def cex1Board : List String :=
  [ "#####"
  , "#@$.#"
  , "#####" ]

def cex1Level : Level := (parseLevel cex1Board).1
def cex1State : State := (parseLevel cex1Board).2.1
def cex1Playable : List Pos := (parseLevel cex1Board).2.2

theorem naiveDeadSquareFreeze_unsound :
    ValidState cex1Level cex1State ∧
    naiveDeadSquareFreeze cex1Level cex1Playable cex1State = true ∧
    Solvable cex1Level cex1State ∧
    isSuperFreezeDeadlock cex1Level cex1Playable cex1State = false := by
  refine ⟨isValidStateBool_sound (by decide), by decide, ?_, by decide⟩
  exact solvable_of_applyMoves (ms := [.right]) (s' := { player := (2, 1), boxes := [(3, 1)] })
    (by decide) (by decide)

-- ============================================================================
-- Heuristic 2: Static Player-Reachability Freeze (Avoiding ALL Current Boxes)
-- ============================================================================

/--
**Unsound Heuristic 2 (`naiveCurrentReachFreeze`):**
Instead of computing player reachability avoiding only the *currently frozen* set `F`,
this heuristic computes `walkable := computeWalkable L playable s.boxes s.player` once,
avoiding *all* boxes currently on the board.
Bug: A box `B` might currently be blocked only because a *movable* box `A` sits in the way!
Once the player pushes `A` aside, the player can walk behind `B` and solve the puzzle.
-/
def naiveCurrentReachFreeze (L : Level) (playable : List Pos) (s : State) : Bool :=
  let live := computeLiveSquares L playable
  let walkable := computeWalkable L playable s.boxes s.player
  let stepFn (F : List Pos) : List Pos :=
    F.filter (fun b => Dir.all.all (dirBlockedBool L live F walkable b))
  let F := iterFixedDown stepFn s.boxes.length (dedupPos s.boxes)
  F.any (fun b => !L.isGoal b)

/--
6×6 counterexample:
- Player `@` at `(3,1)` is sealed in by box `A` at `(3,2)`.
- Box `B` at `(2,2)` cannot currently be reached on its pushing side `(3,2)` because `A` is there.
- Pushing `A` down twice onto `.` `(3,4)` clears the path so the player can push `B` left onto `.` `(1,2)`.
-/
def cex2Board : List String :=
  [ "######"
  , "###@##"
  , "#.$$##"
  , "### ##"
  , "###.##"
  , "######" ]

def cex2Level : Level := (parseLevel cex2Board).1
def cex2State : State := (parseLevel cex2Board).2.1
def cex2Playable : List Pos := (parseLevel cex2Board).2.2

theorem naiveCurrentReachFreeze_unsound :
    ValidState cex2Level cex2State ∧
    naiveCurrentReachFreeze cex2Level cex2Playable cex2State = true ∧
    Solvable cex2Level cex2State ∧
    isSuperFreezeDeadlock cex2Level cex2Playable cex2State = false := by
  refine ⟨isValidStateBool_sound (by decide), by decide, ?_, by decide⟩
  exact solvable_of_applyMoves
    (ms := [.down, .down, .up, .left])
    (s' := { player := (2, 2), boxes := [(1, 2), (3, 4)] })
    (by decide) (by decide)

-- ============================================================================
-- Heuristic 3: "Never Push a Box Off a Goal" (Locking Boxes on Goals)
-- ============================================================================

/--
**Unsound Heuristic 3 (`naiveGoalLock`):**
Simulates the common heuristic of treating any box already standing on a goal (`*`)
as a permanent wall (never allowing it to be pushed off its goal), then checking whether
the remaining boxes become unsolvable (here via `isSuperFreezeDeadlock`).
-/
def lockGoalBoxesLevel (L : Level) (s : State) : Level :=
  { isWall := fun p => L.isWall p || (s.boxes.contains p && L.isGoal p)
    isGoal := L.isGoal }

def lockGoalBoxesState (L : Level) (s : State) : State :=
  { player := s.player
    boxes := s.boxes.filter (fun b => !L.isGoal b) }

def lockGoalBoxesPlayable (L : Level) (playable : List Pos) (s : State) : List Pos :=
  playable.filter (fun p => !(s.boxes.contains p && L.isGoal p))

def naiveGoalLockDeadlock (L : Level) (playable : List Pos) (s : State) : Bool :=
  isSuperFreezeDeadlock (lockGoalBoxesLevel L s) (lockGoalBoxesPlayable L playable s)
    (lockGoalBoxesState L s)

/--
7×4 counterexample:
- Box `*` sits on goal `(4,2)`, blocking box `$` at `(2,2)` from reaching `(4,2)` or `(5,2)`.
- Locking `*` in place makes the remaining box `$` completely unsolvable!
- Real Sokoban solves it by walking around the top bypass, pushing `*` onto `(5,2)`,
  and then pushing `$` onto `(4,2)`.
-/
def cex3Board : List String :=
  [ "#######"
  , "#   ###"
  , "#@$ *.#"
  , "#######" ]

def cex3Level : Level := (parseLevel cex3Board).1
def cex3State : State := (parseLevel cex3Board).2.1
def cex3Playable : List Pos := (parseLevel cex3Board).2.2

theorem naiveGoalLock_unsound :
    ValidState cex3Level cex3State ∧
    naiveGoalLockDeadlock cex3Level cex3Playable cex3State = true ∧
    ¬ Solvable (lockGoalBoxesLevel cex3Level cex3State) (lockGoalBoxesState cex3Level cex3State) ∧
    Solvable cex3Level cex3State ∧
    isSuperFreezeDeadlock cex3Level cex3Playable cex3State = false := by
  refine ⟨isValidStateBool_sound (by decide), by decide, ?_, ?_, by decide⟩
  · refine superFreezeDeadlock_sound
      (playable := lockGoalBoxesPlayable cex3Level cex3Playable cex3State)
      (isValidStateBool_sound (by decide))
      (by decide)
      (isClosedPlayable_sound (by decide))
      (by decide)
      (by decide)
      (by decide)
  · exact solvable_of_applyMoves
      (ms := [.up, .right, .right, .down, .right, .left, .up, .left, .left, .down, .right, .right])
      (s' := { player := (3, 2), boxes := [(4, 2), (5, 2)] })
      (by decide) (by decide)

end Sokoban
