/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs
import Sokoban.DeadSquares
import Sokoban.Freeze
import Sokoban.Solver
import Sokoban.Counterexamples

namespace Sokoban

-- ============================================================================
-- Example 1: Corner Deadlock
-- ============================================================================

def exCornerBoard : List String :=
  [ "#####"
  , "#$. #"
  , "#@  #"
  , "#####" ]

def exCornerLevel : Level := (parseLevel exCornerBoard).1
def exCornerState : State := (parseLevel exCornerBoard).2.1
def exCornerPlayable : List Pos := (parseLevel exCornerBoard).2.2

theorem exCorner_deadlock : ¬ Solvable exCornerLevel exCornerState :=
  cornerDeadlock_sound (isValidStateBool_sound (by decide)) (by decide)

theorem exCorner_bfs_cert_verified :
    solveBFS exCornerLevel exCornerPlayable 200 exCornerState = .unsolvable .initialDeadlock ∧
    checkUnsolvableCert exCornerLevel exCornerPlayable exCornerState .initialDeadlock = true ∧
    ¬ Solvable exCornerLevel exCornerState := by
  refine ⟨by decide, by decide, ?_⟩
  exact checkUnsolvableCert_sound (playable := exCornerPlayable) (cert := .initialDeadlock) (by decide)

-- ============================================================================
-- Example 2: 2×2 Block Deadlock
-- ============================================================================

def ex2x2Board : List String :=
  [ "######"
  , "# $$ #"
  , "# $$ #"
  , "# @..#"
  , "#  ..#"
  , "######" ]

def ex2x2Level : Level := (parseLevel ex2x2Board).1
def ex2x2State : State := (parseLevel ex2x2Board).2.1
def ex2x2Playable : List Pos := (parseLevel ex2x2Board).2.2

theorem ex2x2_deadlock : ¬ Solvable ex2x2Level ex2x2State :=
  block2x2Deadlock_sound (playable := ex2x2Playable) (p := (2, 1))
    (isValidStateBool_sound (by decide))
    (by decide)
    (isClosedPlayable_sound (by decide))
    (by decide)
    (by decide)
    (by decide)

-- ============================================================================
-- Example 3: Simple Dead-Square Corridor (Not in a Corner Yet)
-- ============================================================================

def exDeadSqBoard : List String :=
  [ "######"
  , "#@ $ #"
  , "# ## #"
  , "#  . #"
  , "######" ]

def exDeadSqLevel : Level := (parseLevel exDeadSqBoard).1
def exDeadSqState : State := (parseLevel exDeadSqBoard).2.1
def exDeadSqPlayable : List Pos := (parseLevel exDeadSqBoard).2.2

theorem exDeadSq_not_corner_but_dead :
    exDeadSqState.boxes.any (isCorner exDeadSqLevel) = false ∧
    ¬ Solvable exDeadSqLevel exDeadSqState := by
  refine ⟨by decide, ?_⟩
  exact deadSquareDeadlock_sound (playable := exDeadSqPlayable)
    (isValidStateBool_sound (by decide))
    (by decide)
    (isClosedPlayable_sound (by decide))
    (by decide)
    (by decide)

-- ============================================================================
-- Example 4: Classic 2-Box Freeze Deadlock (No Corner, No Dead Square)
-- ============================================================================

def exZigZagBoard : List String :=
  [ "######"
  , "#.  .#"
  , "##$  #"
  , "# $###"
  , "# @  #"
  , "######" ]

def exZigZagLevel : Level := (parseLevel exZigZagBoard).1
def exZigZagState : State := (parseLevel exZigZagBoard).2.1
def exZigZagPlayable : List Pos := (parseLevel exZigZagBoard).2.2

theorem exZigZag_deadlock :
    exZigZagState.boxes.any (isCorner exZigZagLevel) = false ∧
    isDeadSquareDeadlock exZigZagLevel exZigZagPlayable exZigZagState = false ∧
    ¬ Solvable exZigZagLevel exZigZagState := by
  refine ⟨by decide, by decide, ?_⟩
  exact superFreezeDeadlock_sound (playable := exZigZagPlayable)
    (isValidStateBool_sound (by decide))
    (by decide)
    (isClosedPlayable_sound (by decide))
    (by decide)
    (by decide)
    (by decide)

-- ============================================================================
-- Example 5: Topological Player-Trap Deadlock (Only SuperFreeze Catches It!)
-- ============================================================================

/--
Box `$` at `(2,2)` sits right above goal `.` at `(2,3)`, is NOT in a corner,
is NOT on a dead square, and is NOT locally frozen by walls/boxes (`isClassicFrozen = false`).
Yet pushing it down onto `.` requires standing at `(2,1)`, which is unreachable from `@` at `(2,4)`,
and pushing it up puts it on the top corridor of Simple Dead Squares!
-/
def exPlayerTrapBoard : List String :=
  [ "#####"
  , "#   #"
  , "##$##"
  , "# . #"
  , "# @ #"
  , "#####" ]

def exPlayerTrapLevel : Level := (parseLevel exPlayerTrapBoard).1
def exPlayerTrapState : State := (parseLevel exPlayerTrapBoard).2.1
def exPlayerTrapPlayable : List Pos := (parseLevel exPlayerTrapBoard).2.2

theorem exPlayerTrap_deadlock :
    exPlayerTrapState.boxes.any (isCorner exPlayerTrapLevel) = false ∧
    isDeadSquareDeadlock exPlayerTrapLevel exPlayerTrapPlayable exPlayerTrapState = false ∧
    ¬ Solvable exPlayerTrapLevel exPlayerTrapState := by
  refine ⟨by decide, by decide, ?_⟩
  exact superFreezeDeadlock_sound (playable := exPlayerTrapPlayable)
    (isValidStateBool_sound (by decide))
    (by decide)
    (isClosedPlayable_sound (by decide))
    (by decide)
    (by decide)
    (by decide)

-- ============================================================================
-- Example 6: Solvable Multi-Box Puzzle Verified via `solveBFS`
-- ============================================================================

def exSolvableBoard : List String :=
  [ "######"
  , "# .. #"
  , "# $$ #"
  , "# @  #"
  , "######" ]

def exSolvableLevel : Level := (parseLevel exSolvableBoard).1
def exSolvableState : State := (parseLevel exSolvableBoard).2.1
def exSolvablePlayable : List Pos := (parseLevel exSolvableBoard).2.2

def extractMoves : SolveResult → List Dir
  | .solved ms => ms
  | _ => []

theorem exSolvable_verified :
    verifySolveResult exSolvableLevel exSolvablePlayable exSolvableState
      (solveBFS exSolvableLevel exSolvablePlayable 200 exSolvableState) = true ∧
    Solvable exSolvableLevel exSolvableState := by
  refine ⟨by decide, ?_⟩
  exact verifySolution_sound
    (by decide : verifySolution exSolvableLevel exSolvableState
      (extractMoves (solveBFS exSolvableLevel exSolvablePlayable 200 exSolvableState)) = true)

-- ============================================================================
-- Example 7: Unsolvable Puzzle Requiring Search (Not Dead at Turn 0)
-- ============================================================================

/--
At turn 0, `isSuperFreezeDeadlock = false`: boxes can still be pushed onto live squares.
Yet `solveBFS` explores the entire deadlock-pruned state space (14 states) and emits
a closed invariant certificate, verified by `checkUnsolvableCert_sound`.
-/
def exUnsolvableBoard : List String :=
  [ "######"
  , "#.. @#"
  , "# $$ #"
  , "#  # #"
  , "######" ]

def exUnsolvableLevel : Level := (parseLevel exUnsolvableBoard).1
def exUnsolvableState : State := (parseLevel exUnsolvableBoard).2.1
def exUnsolvablePlayable : List Pos := (parseLevel exUnsolvableBoard).2.2

def extractCert : SolveResult → UnsolvableCert
  | .unsolvable cert => cert
  | _ => .closedRegion []

theorem exUnsolvable_verified :
    isSuperFreezeDeadlock exUnsolvableLevel exUnsolvablePlayable exUnsolvableState = false ∧
    checkUnsolvableCert exUnsolvableLevel exUnsolvablePlayable exUnsolvableState
      (extractCert (solveBFS exUnsolvableLevel exUnsolvablePlayable 200 exUnsolvableState)) = true ∧
    ¬ Solvable exUnsolvableLevel exUnsolvableState := by
  refine ⟨by decide, by decide, ?_⟩
  exact checkUnsolvableCert_sound
    (by decide : checkUnsolvableCert exUnsolvableLevel exUnsolvablePlayable exUnsolvableState
      (extractCert (solveBFS exUnsolvableLevel exUnsolvablePlayable 200 exUnsolvableState)) = true)

/-- All 10 bundled example and counterexample boards pass the strict XSB parser. -/
theorem all_boards_parseLevelStrict :
    [ exCornerBoard, ex2x2Board, exDeadSqBoard, exZigZagBoard, exPlayerTrapBoard,
      exSolvableBoard, exUnsolvableBoard, cex1Board, cex2Board, cex3Board ].all
        (fun b => (parseLevelStrict b).isSome) = true := by
  decide

-- ============================================================================
-- Axiom Audit
-- ============================================================================

#print axioms cornerDeadlock_sound
#print axioms deadSquareDeadlock_sound
#print axioms block2x2Deadlock_sound
#print axioms superFreezeDeadlock_sound
#print axioms checkUnsolvableCert_sound
#print axioms verifySolution_sound
#print axioms verifySolveResult_solved_sound
#print axioms verifySolveResult_unsolvable_sound
#print axioms naiveDeadSquareFreeze_unsound
#print axioms naiveCurrentReachFreeze_unsound
#print axioms naiveGoalLock_unsound
#print axioms exCorner_bfs_cert_verified
#print axioms exSolvable_verified
#print axioms exUnsolvable_verified
#print axioms all_boards_parseLevelStrict

end Sokoban
