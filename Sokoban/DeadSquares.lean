/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs
import Sokoban.Fixpoint

namespace Sokoban

/-- A single-box push ignoring all other boxes (used for static dead-square analysis). -/
def SingleBoxStep (L : Level) (b b' : Pos) : Prop :=
  ∃ d : Dir, L.isWall (step b d.opp) = false ∧ L.isWall (step b d) = false ∧ b' = step b d

/-- Multi-step reachability of a single box ignoring all other boxes. -/
inductive SingleBoxReach (L : Level) : Pos → Pos → Prop where
  | refl (b : Pos) : SingleBoxReach L b b
  | step {b₁ b₂ b₃ : Pos} : SingleBoxStep L b₁ b₂ → SingleBoxReach L b₂ b₃ → SingleBoxReach L b₁ b₃

theorem SingleBoxReach.trans {L : Level} {b₁ b₂ b₃ : Pos}
    (h₁₂ : SingleBoxReach L b₁ b₂) (h₂₃ : SingleBoxReach L b₂ b₃) :
    SingleBoxReach L b₁ b₃ := by
  induction h₁₂ with
  | refl => exact h₂₃
  | step hs _ ih => exact SingleBoxReach.step hs (ih h₂₃)

/-- Every box in a valid state can be tracked forward across one legal step. -/
theorem Step.tracks_box {L : Level} {s₁ s₂ : State}
    (hv : ValidState L s₁) (hs : Step L s₁ s₂) :
    ∀ b ∈ s₁.boxes, ∃ b' ∈ s₂.boxes, SingleBoxReach L b b' := by
  revert hv
  cases hs with
  | walk d s hw hnb =>
    intro _ b hb
    exact ⟨b, hb, SingleBoxReach.refl b⟩
  | push d _ hbox hw hnb =>
    intro hv b hb
    by_cases heq : b = step s₁.player d
    · subst heq
      refine ⟨step (step s₁.player d) d, (mem_moveBox hbox).mpr (.inl rfl), ?_⟩
      refine SingleBoxReach.step ⟨d, ?_, hw, rfl⟩ (SingleBoxReach.refl _)
      rw [step_opp]
      exact hv.1
    · exact ⟨b, (mem_moveBox hbox).mpr (.inr ⟨hb, heq⟩), SingleBoxReach.refl b⟩

/-- Every box in a valid state can be tracked forward to some box in any reachable state. -/
theorem reach_tracks_box {L : Level} {s s' : State}
    (hv : ValidState L s) (hr : Reach L s s') :
    ∀ b ∈ s.boxes, ∃ b' ∈ s'.boxes, SingleBoxReach L b b' := by
  induction hr with
  | refl =>
    intro b hb
    exact ⟨b, hb, SingleBoxReach.refl b⟩
  | @step s₁ s₂ s₃ hs _ ih =>
    intro b hb₁
    have hv₂ : ValidState L s₂ := hs.preserves_valid hv
    rcases hs.tracks_box hv b hb₁ with ⟨b₂, hb₂, hr₁₂⟩
    rcases ih hv₂ b₂ hb₂ with ⟨b₃, hb₃, hr₂₃⟩
    exact ⟨b₃, hb₃, hr₁₂.trans hr₂₃⟩

/-- If a box cannot reach any goal even ignoring all other boxes, the state is unsolvable. -/
theorem not_singleBoxReach_goal_deadlock {L : Level} {s : State} {b : Pos}
    (hv : ValidState L s) (hb : b ∈ s.boxes)
    (hdead : ∀ g, SingleBoxReach L b g → L.isGoal g = false) :
    ¬ Solvable L s := by
  rintro ⟨s', hr, hsolved⟩
  rcases reach_tracks_box hv hr b hb with ⟨b', hb', hbr⟩
  have hgoal := hsolved b' hb'
  have hnot := hdead b' hbr
  simp_all

/-- Simple corner check: non-goal square blocked on at least one horizontal and one vertical side. -/
def isCorner (L : Level) (b : Pos) : Bool :=
  !L.isGoal b &&
    (L.isWall (step b .left) || L.isWall (step b .right)) &&
    (L.isWall (step b .up) || L.isWall (step b .down))

private theorem corner_no_singleBoxStep {L : Level} {b b' : Pos}
    (hc : isCorner L b = true) (hs : SingleBoxStep L b b') : False := by
  simp only [isCorner, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  rcases hc with ⟨⟨_, hlr⟩, hud⟩
  rcases hs with ⟨d, hw1, hw2, _⟩
  cases d <;> simp [Dir.opp] at hw1 hw2
  · rcases hud with hu | hd <;> simp_all
  · rcases hud with hu | hd <;> simp_all
  · rcases hlr with hl | hr <;> simp_all
  · rcases hlr with hl | hr <;> simp_all

theorem cornerDeadlock_sound {L : Level} {s : State}
    (hv : ValidState L s) (hc : s.boxes.any (isCorner L) = true) :
    ¬ Solvable L s := by
  simp only [List.any_eq_true] at hc
  rcases hc with ⟨b, hb, hcb⟩
  refine not_singleBoxReach_goal_deadlock hv hb ?_
  intro g hbr
  cases hbr with
  | refl =>
    simp only [isCorner, Bool.and_eq_true, Bool.not_eq_true'] at hcb
    exact hcb.1.1
  | step hs _ =>
    exact False.elim (corner_no_singleBoxStep hcb hs)

/-- A list of playable positions is closed under stepping to non-wall neighbors. -/
def ClosedPlayable (L : Level) (playable : List Pos) : Prop :=
  ∀ p ∈ playable, ∀ d : Dir, L.isWall (step p d) = false → step p d ∈ playable

/-- Executable checker for `ClosedPlayable`. -/
def isClosedPlayable (L : Level) (playable : List Pos) : Bool :=
  playable.all (fun p => Dir.all.all (fun d => L.isWall (step p d) || playable.contains (step p d)))

theorem isClosedPlayable_sound {L : Level} {playable : List Pos}
    (h : isClosedPlayable L playable = true) : ClosedPlayable L playable := by
  simp only [isClosedPlayable, List.all_eq_true, Bool.or_eq_true] at h
  intro p hp d hw
  have h1 := h p hp d (Dir.mem_all d)
  rcases h1 with hw' | hc
  · simp_all
  · exact List.contains_iff_mem.mp hc

theorem singleBoxReach_mem_playable {L : Level} {playable : List Pos}
    (hclosed : ClosedPlayable L playable) {b g : Pos}
    (hb : b ∈ playable) (hr : SingleBoxReach L b g) : g ∈ playable := by
  induction hr with
  | refl => exact hb
  | step hs _ ih =>
    rcases hs with ⟨d, _, hw, rfl⟩
    exact ih (hclosed _ hb d hw)

/-- One backward-BFS step computing squares from which a single box can reach a goal. -/
def liveStep (L : Level) (playable live : List Pos) : List Pos :=
  playable.filter (fun p =>
    live.contains p ||
    Dir.all.any (fun d =>
      !L.isWall (step p d.opp) && !L.isWall (step p d) && live.contains (step p d)))

/-- All squares in `playable` from which a single box can reach some goal in `playable`. -/
def computeLiveSquares (L : Level) (playable : List Pos) : List Pos :=
  iterFixedUp (liveStep L playable) playable.length (playable.filter L.isGoal)

private theorem liveStep_props {L : Level} {playable : List Pos}
    (hp : playable.Nodup) :
    ∀ ys, SubPos ys playable →
      SubPos ys (liveStep L playable ys) ∧
      SubPos (liveStep L playable ys) playable ∧
      (liveStep L playable ys).Nodup := by
  intro ys hsub
  refine ⟨?_, ?_, nodup_filter hp⟩
  · intro x hx
    simp only [liveStep, List.mem_filter, Bool.or_eq_true]
    exact ⟨hsub x hx, .inl (List.contains_iff_mem.mpr hx)⟩
  · intro x hx
    simp only [liveStep, List.mem_filter] at hx
    exact hx.1

theorem singleBoxReach_goal_mem_liveSquares {L : Level} {playable : List Pos}
    (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    {b g : Pos} (hb : b ∈ playable) (hr : SingleBoxReach L b g) (hg : L.isGoal g = true) :
    b ∈ computeLiveSquares L playable := by
  let start := playable.filter L.isGoal
  have hstart_sub : SubPos start playable := fun x hx => (List.mem_filter.mp hx).1
  have hstart_nodup : start.Nodup := nodup_filter hp
  have hprops_nd : ∀ ys, SubPos ys playable → ys.Nodup →
      SubPos ys (liveStep L playable ys) ∧
      SubPos (liveStep L playable ys) playable ∧
      (liveStep L playable ys).Nodup :=
    fun ys hys _ => liveStep_props hp ys hys
  have hprops2 : ∀ ys, SubPos ys playable →
      SubPos ys (liveStep L playable ys) ∧ SubPos (liveStep L playable ys) playable :=
    fun ys hys => ⟨(liveStep_props hp ys hys).1, (liveStep_props hp ys hys).2.1⟩
  have hfix := iterFixedUp_fixpoint (f := liveStep L playable) hp hprops_nd playable.length start
    hstart_sub hstart_nodup (by omega)
  have hsub_start : SubPos start (computeLiveSquares L playable) :=
    iterFixedUp_subset_start hprops2 playable.length start hstart_sub
  induction hr with
  | refl =>
    exact hsub_start _ (List.mem_filter.mpr ⟨hb, hg⟩)
  | @step b₁ b₂ b₃ hs _ ih =>
    rcases hs with ⟨d, hw1, hw2, rfl⟩
    have hb₂ : step b₁ d ∈ playable := hclosed b₁ hb d hw2
    have hmem2 : step b₁ d ∈ computeLiveSquares L playable := ih hb₂ hg
    refine (hfix b₁).mp ?_
    simp only [liveStep, List.mem_filter, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      Bool.not_eq_true']
    refine ⟨hb, .inr ⟨d, Dir.mem_all d, ⟨hw1, hw2⟩, List.contains_iff_mem.mpr hmem2⟩⟩

/-- Executable Simple Dead Square deadlock detector. -/
def isDeadSquareDeadlock (L : Level) (playable : List Pos) (s : State) : Bool :=
  let live := computeLiveSquares L playable
  s.boxes.any (fun b => !live.contains b)

theorem deadSquareDeadlock_sound {L : Level} {playable : List Pos} {s : State}
    (hv : ValidState L s) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hbox : ∀ b ∈ s.boxes, b ∈ playable)
    (hdead : isDeadSquareDeadlock L playable s = true) :
    ¬ Solvable L s := by
  simp only [isDeadSquareDeadlock, List.any_eq_true, Bool.not_eq_true'] at hdead
  rcases hdead with ⟨b, hb, hnot⟩
  refine not_singleBoxReach_goal_deadlock hv hb ?_
  intro g hbr
  cases hg : L.isGoal g
  · rfl
  · have hmem := singleBoxReach_goal_mem_liveSquares hp hclosed (hbox b hb) hbr hg
    have hc : (computeLiveSquares L playable).contains b = true := List.contains_iff_mem.mpr hmem
    simp_all

end Sokoban
