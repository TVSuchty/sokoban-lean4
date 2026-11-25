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

Below we formalize three plausible, tempting heuristics that serve as concrete regression
cases for common solver-pruning mistakes, and prove formally in Lean 4 that **all three are unsound** —
while our verified `isSuperFreezeDeadlock` correctly returns `false` on every one of them.
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
8×4 counterexample:
- Box `*` sits on goal `(4,2)`, blocking box `$` at `(2,2)` from reaching `(4,2)` or `(6,2)`.
- Even under the weaker rule that allows sliding a box between adjacent goals and forbids only
  pushing a box from a goal onto *non-goal floor*, the puzzle is still unsolvable (since `(5,2)` is
  non-goal floor)!
- Real Sokoban solves it in 14 moves by walking around the top bypass, pushing `*` off `(4,2)` onto
  non-goal floor `(5,2)` and then onto `(6,2)`, and finally pushing `$` onto `(4,2)`.
-/
def cex3Board : List String :=
  [ "########"
  , "#   ####"
  , "#@$ * .#"
  , "########" ]

def cex3Level : Level := (parseLevel cex3Board).1
def cex3State : State := (parseLevel cex3Board).2.1
def cex3Playable : List Pos := (parseLevel cex3Board).2.2

/-- Restricted semantics forbidding pushes from a goal square onto a non-goal square. -/
inductive StepNoOffGoalPush (L : Level) : State → State → Prop where
  | walk (d : Dir) (s : State)
      (hw : L.isWall (step s.player d) = false)
      (hb : step s.player d ∉ s.boxes) :
      StepNoOffGoalPush L s { player := step s.player d, boxes := s.boxes }
  | push (d : Dir) (s : State)
      (hb : step s.player d ∈ s.boxes)
      (hw : L.isWall (step (step s.player d) d) = false)
      (hnb : step (step s.player d) d ∉ s.boxes)
      (hoff : L.isGoal (step s.player d) = true → L.isGoal (step (step s.player d) d) = true) :
      StepNoOffGoalPush L s
        { player := step s.player d
          boxes := moveBox s.boxes (step s.player d) (step (step s.player d) d) }

inductive ReachNoOffGoalPush (L : Level) : State → State → Prop where
  | refl (s : State) : ReachNoOffGoalPush L s s
  | step {s₁ s₂ s₃ : State} :
      StepNoOffGoalPush L s₁ s₂ → ReachNoOffGoalPush L s₂ s₃ → ReachNoOffGoalPush L s₁ s₃

def SolvableNoOffGoalPush (L : Level) (s : State) : Prop :=
  ∃ s', ReachNoOffGoalPush L s s' ∧ IsSolved L s'

private def lock42Level : Level :=
  { isWall := fun p => cex3Level.isWall p || p == (4, 2)
    isGoal := cex3Level.isGoal }

private def lock42State (s : State) : State :=
  { player := s.player, boxes := s.boxes.filter (fun b => b != (4, 2)) }

private def lock42Playable : List Pos :=
  cex3Playable.filter (fun p => p != (4, 2))

private theorem filter_moveBox_comm (bs : List Pos) (p k dest : Pos)
    (hp : p ≠ k) (hdest : dest ≠ k) :
    (moveBox bs p dest).filter (fun b => b != k) =
    moveBox (bs.filter (fun b => b != k)) p dest := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [moveBox, List.map_cons, List.filter_cons] at ih ⊢
    by_cases hak : a = k
    · have h1 : (a != k) = false := by subst hak; simp
      have hap : (a == p) = false := beq_false_of_ne (fun h => hp (h.symm.trans hak))
      rw [hap]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih
    · have hk1 : (a != k) = true := bne_iff_ne.mpr hak
      by_cases hap : a = p
      · have hbeq : (a == p) = true := beq_iff_eq.mpr hap
        have hk2 : (dest != k) = true := bne_iff_ne.mpr hdest
        rw [hbeq, hk1]
        simp only [↓reduceIte, List.map_cons]
        rw [hk2, hbeq]
        simp only [↓reduceIte]
        exact congrArg (dest :: ·) ih
      · have hbeq : (a == p) = false := beq_false_of_ne hap
        rw [hbeq, hk1]
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons]
        rw [hk1, hbeq]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (a :: ·) ih

private theorem cex3_stepNoOffGoalPush_keeps_42 {s s' : State}
    (h42 : (4, 2) ∈ s.boxes) (hs : StepNoOffGoalPush cex3Level s s') :
    Step lock42Level (lock42State s) (lock42State s') ∧ (4, 2) ∈ s'.boxes := by
  revert h42
  cases hs with
  | walk d _ hw hb =>
    intro h42
    have hne : step s.player d ≠ (4, 2) := fun heq => hb (heq ▸ h42)
    have hw' : lock42Level.isWall (step s.player d) = false := by
      simp [lock42Level, hw, beq_false_of_ne hne]
    have hb' : step s.player d ∉ (lock42State s).boxes := by
      intro hm
      exact hb (List.mem_filter.mp hm).1
    exact ⟨Step.walk d (lock42State s) hw' hb', h42⟩
  | push d _ hb hw hnb hoff =>
    intro h42
    have hnot42 : step s.player d ≠ (4, 2) := by
      intro heq
      have hgoal42 : cex3Level.isGoal (4, 2) = true := by decide
      rw [heq] at hw hoff
      cases d
      · have : cex3Level.isWall (step (4, 2) .up) = true := by decide
        simp_all
      · have : cex3Level.isWall (step (4, 2) .down) = true := by decide
        simp_all
      · have : cex3Level.isGoal (step (4, 2) .left) = false := by decide
        have := hoff hgoal42
        simp_all
      · have : cex3Level.isGoal (step (4, 2) .right) = false := by decide
        have := hoff hgoal42
        simp_all
    have hdest42 : step (step s.player d) d ≠ (4, 2) := fun heq => hnb (heq ▸ h42)
    have hb' : step s.player d ∈ (lock42State s).boxes :=
      List.mem_filter.mpr ⟨hb, bne_iff_ne.mpr hnot42⟩
    have hw' : lock42Level.isWall (step (step s.player d) d) = false := by
      simp [lock42Level, hw, beq_false_of_ne hdest42]
    have hnb' : step (step s.player d) d ∉ (lock42State s).boxes := by
      intro hm
      exact hnb (List.mem_filter.mp hm).1
    have h42' : (4, 2) ∈ moveBox s.boxes (step s.player d) (step (step s.player d) d) :=
      (mem_moveBox hb).mpr (.inr ⟨h42, hnot42.symm⟩)
    refine ⟨?_, h42'⟩
    simp only [lock42State]
    rw [filter_moveBox_comm s.boxes (step s.player d) (4, 2) (step (step s.player d) d) hnot42 hdest42]
    exact Step.push d (lock42State s) hb' hw' hnb'

theorem naiveGoalLock_unsound :
    ValidState cex3Level cex3State ∧
    naiveGoalLockDeadlock cex3Level cex3Playable cex3State = true ∧
    ¬ Solvable (lockGoalBoxesLevel cex3Level cex3State) (lockGoalBoxesState cex3Level cex3State) ∧
    ¬ SolvableNoOffGoalPush cex3Level cex3State ∧
    Solvable cex3Level cex3State ∧
    isSuperFreezeDeadlock cex3Level cex3Playable cex3State = false := by
  refine ⟨isValidStateBool_sound (by decide), by decide, ?_, ?_, ?_, by decide⟩
  · refine superFreezeDeadlock_sound
      (playable := lockGoalBoxesPlayable cex3Level cex3Playable cex3State)
      (isValidStateBool_sound (by decide))
      (by decide)
      (isClosedPlayable_sound (by decide))
      (by decide)
      (by decide)
      (by decide)
  · rintro ⟨s_end, hr, hsol⟩
    have hlock_unsol : ¬ Solvable lock42Level (lock42State cex3State) := by
      refine superFreezeDeadlock_sound
        (playable := lock42Playable)
        (isValidStateBool_sound (by decide))
        (by decide)
        (isClosedPlayable_sound (by decide))
        (by decide)
        (by decide)
        (by decide)
    have h42_init : (4, 2) ∈ cex3State.boxes := by decide
    suffices hreach : ∀ {s₁ s₂ : State}, ReachNoOffGoalPush cex3Level s₁ s₂ →
        (4, 2) ∈ s₁.boxes → Reach lock42Level (lock42State s₁) (lock42State s₂) by
      refine hlock_unsol ⟨lock42State s_end, hreach hr h42_init, ?_⟩
      intro b hb
      exact hsol b (List.mem_filter.mp hb).1
    intro s₁ s₂ hr₁₂ h42
    induction hr₁₂ with
    | refl => exact Reach.refl _
    | step hs _ ih =>
      rcases cex3_stepNoOffGoalPush_keeps_42 h42 hs with ⟨hstep', h42'⟩
      exact Reach.step hstep' (ih h42')
  · exact solvable_of_applyMoves
      (ms := [.up, .right, .right, .down, .right, .right, .left, .left, .up, .left, .left, .down, .right, .right])
      (s' := { player := (3, 2), boxes := [(4, 2), (6, 2)] })
      (by decide) (by decide)

end Sokoban
