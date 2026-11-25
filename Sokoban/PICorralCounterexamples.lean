/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs
import Sokoban.DeadSquares
import Sokoban.Freeze
import Sokoban.Solver
import Sokoban.PICorral

namespace Sokoban

/-!
# Merged PI-Corral Showcase & Real-World Implementation Bug Counterexamples

1. **`exMergedPICorral_verified`**: Demonstrates a board where *neither* individual pocket forms a
   PI-Corral on its own, yet merging them produces a valid `IsPICorral` that preserves exact
   2-push optimality (`piCorral_push_optimal`).
2. **Real-World Bug 1 (`piCorral_notStripExtI_unsound`)**: Forgetting to strip external boxes
   `s₀.boxes \ B` in the **I-Corral** check (falsely ignoring an outward push blocked only by an
   external box) leads to pruning every winning line on a 2-push solvable board (`picex1Board`).
3. **Real-World Bug 2 (`piCorral_stripExtP_unsound`)**: Stripping external boxes in the
   **P-Corral** player-reachability check makes a blocked inward push look reachable, turning a
   5-move solvable board (`picex2Board`) into a false dynamic deadlock (`piCorralInwardPushes = []`).
4. **Real-World Bug 3 (`piCorral_noUnsolvedObligation_unsound`)**: Omitting the unsolved-box check
   (`∃ b ∈ B, L.isGoal b = false`) lets an already-solved corral force a fatal push off a goal
   into a dead corner on a 3-move solvable board (`picex3Board`).

Together, Bugs 1 & 2 formally nail down the asymmetric external-box rule in YASS/SokoBoy:
external boxes **must** be stripped in the I-check, and **must not** be stripped in the P-check!
-/

-- ============================================================================
-- 1. Merged-Only PI-Corral Showcase
-- ============================================================================

def exMergedBoard : List String :=
  [ "######"
  , "## .##"
  , "# # ##"
  , "#* $ #"
  , "#  @*#"
  , "######" ]

def exMergedLevel : Level := (parseLevel exMergedBoard).1
def exMergedState : State := (parseLevel exMergedBoard).2.1
def exMergedPlayable : List Pos := (parseLevel exMergedBoard).2.2

def exMergedC1 : List Pos := [(2, 1), (3, 1), (3, 2)]
def exMergedB1 : List Pos := [(3, 3)]
def exMergedC2 : List Pos := [(4, 3)]
def exMergedB2 : List Pos := [(3, 3), (4, 4)]

theorem exMergedPICorral_verified :
    (parseLevelStrict exMergedBoard).isSome = true ∧
    isPICorralBool exMergedLevel exMergedPlayable (computeLiveSquares exMergedLevel exMergedPlayable)
      exMergedState exMergedC1 exMergedB1 = false ∧
    isPICorralBool exMergedLevel exMergedPlayable (computeLiveSquares exMergedLevel exMergedPlayable)
      exMergedState exMergedC2 exMergedB2 = false ∧
    (findPICorral exMergedLevel exMergedPlayable (computeLiveSquares exMergedLevel exMergedPlayable)
      exMergedState).isSome = true ∧
    (∀ C B,
      findPICorral exMergedLevel exMergedPlayable (computeLiveSquares exMergedLevel exMergedPlayable)
        exMergedState = some (C, B) →
      IsPICorral exMergedLevel (computeLiveSquares exMergedLevel exMergedPlayable) exMergedState C B) ∧
    (∃ s_end, ReachPushes exMergedLevel exMergedState s_end 2 ∧ IsSolved exMergedLevel s_end) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro C B hfind
    -- Unfold `findPICorral` concretely by `decide`:
    have hok : isPICorralBool exMergedLevel exMergedPlayable
        (computeLiveSquares exMergedLevel exMergedPlayable) exMergedState C B = true := by
      have hcheck :
          (match findPICorral exMergedLevel exMergedPlayable
              (computeLiveSquares exMergedLevel exMergedPlayable) exMergedState with
          | none => false
          | some (c, b) => isPICorralBool exMergedLevel exMergedPlayable
              (computeLiveSquares exMergedLevel exMergedPlayable) exMergedState c b) = true := by
        decide
      rw [hfind] at hcheck
      exact hcheck
    exact isPICorralBool_sound hok
  · refine ⟨{ player := (3, 2), boxes := [(1, 3), (3, 1), (4, 4)] }, ?_,
        isSolvedBool_sound (by decide)⟩
    exact ReachPushes.push (d := .up) (by decide) (by decide) (by decide)
      (ReachPushes.push (d := .up) (by decide) (by decide) (by decide) (ReachPushes.refl _))

-- ============================================================================
-- 2. Bug 1: Forgetting to Strip External Boxes in the I-Corral Check
-- ============================================================================

/-- Buggy PI-Corral check using `s₀.boxes` instead of `B` in the I-Corral (outward-push) test. -/
def naivePICorralNoStripI (L : Level) (playable live : List Pos) (s₀ : State)
    (C B : List Pos) : Bool :=
  let walkable := computeWalkable L playable s₀.boxes s₀.player
  !C.isEmpty &&
  !B.isEmpty &&
  B.all (fun b => s₀.boxes.contains b) &&
  C.all (fun p => !L.isWall p && !s₀.boxes.contains p) &&
  !C.contains s₀.player &&
  C.all (fun p => Dir.all.all (fun d =>
    L.isWall (step p d) || B.contains (step p d) || C.contains (step p d))) &&
  B.any (fun b => !L.isGoal b) &&
  B.all (fun b => Dir.all.all (fun d =>
    let pushPos := step b d.opp
    let dest := step b d
    if !L.isWall pushPos && !s₀.boxes.contains pushPos && !C.contains pushPos &&
       !L.isWall dest && !s₀.boxes.contains dest && live.contains dest then
      C.contains dest && walkable.contains pushPos
    else true))

def picex1Board : List String :=
  [ "######"
  , "# .# #"
  , "##$$.#"
  , "#  # #"
  , "#@*  #"
  , "######" ]

def picex1Level : Level := (parseLevel picex1Board).1
def picex1State : State := (parseLevel picex1Board).2.1
def picex1Playable : List Pos := (parseLevel picex1Board).2.2
def picex1C : List Pos := [(3, 4), (4, 1), (4, 2), (4, 3), (4, 4)]
def picex1B : List Pos := [(2, 4), (3, 2)]

/-- State reached after executing the sole inward push `((2, 4), .right)` allowed by `naivePICorralNoStripI`. -/
def picex1AfterPush : State :=
  { player := (2, 4), boxes := [(2, 2), (3, 2), (3, 4)] }

private def extractCertPI : SolveResult → UnsolvableCert
  | .unsolvable c => c
  | _ => .closedRegion []

theorem piCorral_notStripExtI_unsound :
    (parseLevelStrict picex1Board).isSome = true ∧
    naivePICorralNoStripI picex1Level picex1Playable (computeLiveSquares picex1Level picex1Playable)
      picex1State picex1C picex1B = true ∧
    piCorralInwardPushes picex1Level picex1Playable (computeLiveSquares picex1Level picex1Playable)
      picex1State picex1C picex1B = [((2, 4), .right)] ∧
    execDir picex1Level picex1State .right = some picex1AfterPush ∧
    ¬ Solvable picex1Level picex1AfterPush ∧
    Solvable picex1Level picex1State ∧
    isPICorralBool picex1Level picex1Playable (computeLiveSquares picex1Level picex1Playable)
      picex1State picex1C picex1B = false := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, by decide⟩
  · exact checkUnsolvableCert_sound
      (by decide : checkUnsolvableCert picex1Level picex1Playable picex1AfterPush
        (extractCertPI (solveBFS picex1Level picex1Playable 200 picex1AfterPush)) = true)
  · exact solvable_of_applyMoves
      (ms := [.up, .right, .up, .right])
      (s' := { player := (3, 2), boxes := [(2, 1), (4, 2), (2, 4)] })
      (by decide) (by decide)

-- ============================================================================
-- 3. Bug 2: Stripping External Boxes in the P-Corral Player-Reachability Check
-- ============================================================================

/-- Buggy PI-Corral check using `computeWalkable ... B` instead of `s₀.boxes` in the P-Corral test. -/
def naivePICorralStripP (L : Level) (playable live : List Pos) (s₀ : State)
    (C B : List Pos) : Bool :=
  let walkable := computeWalkable L playable B s₀.player
  !C.isEmpty &&
  !B.isEmpty &&
  B.all (fun b => s₀.boxes.contains b) &&
  C.all (fun p => !L.isWall p && !s₀.boxes.contains p) &&
  !C.contains s₀.player &&
  C.all (fun p => Dir.all.all (fun d =>
    L.isWall (step p d) || B.contains (step p d) || C.contains (step p d))) &&
  B.any (fun b => !L.isGoal b) &&
  B.all (fun b => Dir.all.all (fun d =>
    let pushPos := step b d.opp
    let dest := step b d
    if !L.isWall pushPos && !B.contains pushPos && !C.contains pushPos &&
       !L.isWall dest && !B.contains dest && live.contains dest then
      C.contains dest && walkable.contains pushPos
    else true))

def picex2Board : List String :=
  [ "######"
  , "#@$. #"
  , "##   #"
  , "#   ##"
  , "## $.#"
  , "######" ]

def picex2Level : Level := (parseLevel picex2Board).1
def picex2State : State := (parseLevel picex2Board).2.1
def picex2Playable : List Pos := (parseLevel picex2Board).2.2
def picex2C : List Pos := [(4, 4)]
def picex2B : List Pos := [(3, 4)]

theorem piCorral_stripExtP_unsound :
    (parseLevelStrict picex2Board).isSome = true ∧
    naivePICorralStripP picex2Level picex2Playable (computeLiveSquares picex2Level picex2Playable)
      picex2State picex2C picex2B = true ∧
    piCorralInwardPushes picex2Level picex2Playable (computeLiveSquares picex2Level picex2Playable)
      picex2State picex2C picex2B = [] ∧
    Solvable picex2Level picex2State ∧
    isPICorralBool picex2Level picex2Playable (computeLiveSquares picex2Level picex2Playable)
      picex2State picex2C picex2B = false := by
  refine ⟨by decide, by decide, by decide, ?_, by decide⟩
  exact solvable_of_applyMoves
    (ms := [.right, .down, .down, .down, .right])
    (s' := { player := (3, 4), boxes := [(3, 1), (4, 4)] })
    (by decide) (by decide)

-- ============================================================================
-- 4. Bug 3: Omitting the Unsolved-Corral Obligation
-- ============================================================================

/-- Buggy PI-Corral check missing `B.any (fun b => !L.isGoal b)`. -/
def naivePICorralNoUnsolved (L : Level) (playable live : List Pos) (s₀ : State)
    (C B : List Pos) : Bool :=
  let walkable := computeWalkable L playable s₀.boxes s₀.player
  !C.isEmpty &&
  !B.isEmpty &&
  B.all (fun b => s₀.boxes.contains b) &&
  C.all (fun p => !L.isWall p && !s₀.boxes.contains p) &&
  !C.contains s₀.player &&
  C.all (fun p => Dir.all.all (fun d =>
    L.isWall (step p d) || B.contains (step p d) || C.contains (step p d))) &&
  B.all (fun b => Dir.all.all (fun d =>
    let pushPos := step b d.opp
    let dest := step b d
    if !L.isWall pushPos && !B.contains pushPos && !C.contains pushPos &&
       !L.isWall dest && !B.contains dest && live.contains dest then
      C.contains dest && walkable.contains pushPos
    else true))

def picex3Board : List String :=
  [ "######"
  , "#  .##"
  , "# @$##"
  , "#   *#"
  , "# ## #"
  , "######" ]

def picex3Level : Level := (parseLevel picex3Board).1
def picex3State : State := (parseLevel picex3Board).2.1
def picex3Playable : List Pos := (parseLevel picex3Board).2.2
def picex3C : List Pos := [(4, 4)]
def picex3B : List Pos := [(4, 3)]

theorem piCorral_noUnsolvedObligation_unsound :
    (parseLevelStrict picex3Board).isSome = true ∧
    naivePICorralNoUnsolved picex3Level picex3Playable (computeLiveSquares picex3Level picex3Playable)
      picex3State picex3C picex3B = true ∧
    piCorralInwardPushes picex3Level picex3Playable (computeLiveSquares picex3Level picex3Playable)
      picex3State picex3C picex3B = [] ∧
    Solvable picex3Level picex3State ∧
    isPICorralBool picex3Level picex3Playable (computeLiveSquares picex3Level picex3Playable)
      picex3State picex3C picex3B = false := by
  refine ⟨by decide, by decide, by decide, ?_, by decide⟩
  exact solvable_of_applyMoves
    (ms := [.down, .right, .up])
    (s' := { player := (3, 2), boxes := [(3, 1), (4, 3)] })
    (by decide) (by decide)

-- ============================================================================
-- Axiom Audit
-- ============================================================================

#print axioms piCorral_push_optimal
#print axioms piCorral_solvable_preservation
#print axioms piCorral_deadlock_sound
#print axioms isPICorralBool_sound
#print axioms exMergedPICorral_verified
#print axioms piCorral_notStripExtI_unsound
#print axioms piCorral_stripExtP_unsound
#print axioms piCorral_noUnsolvedObligation_unsound

end Sokoban
