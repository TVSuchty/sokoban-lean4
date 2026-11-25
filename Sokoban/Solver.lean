/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs
import Sokoban.DeadSquares
import Sokoban.Freeze

namespace Sokoban

/-- Two states are equivalent iff the player position coincides and box sets match. -/
def StateEquiv (s₁ s₂ : State) : Prop :=
  s₁.player = s₂.player ∧ ∀ b, b ∈ s₁.boxes ↔ b ∈ s₂.boxes

theorem StateEquiv.refl (s : State) : StateEquiv s s :=
  ⟨rfl, fun _ => Iff.rfl⟩

theorem StateEquiv.symm {s₁ s₂ : State} (h : StateEquiv s₁ s₂) : StateEquiv s₂ s₁ :=
  ⟨h.1.symm, fun b => (h.2 b).symm⟩

theorem StateEquiv.trans {s₁ s₂ s₃ : State}
    (h₁₂ : StateEquiv s₁ s₂) (h₂₃ : StateEquiv s₂ s₃) : StateEquiv s₁ s₃ :=
  ⟨h₁₂.1.trans h₂₃.1, fun b => (h₁₂.2 b).trans (h₂₃.2 b)⟩

/-- Executable state-equivalence check (up to box-list permutation/duplicates). -/
def stateEquivBool (s₁ s₂ : State) : Bool :=
  (s₁.player == s₂.player) &&
  s₁.boxes.all (fun b => s₂.boxes.contains b) &&
  s₂.boxes.all (fun b => s₁.boxes.contains b)

theorem stateEquivBool_sound {s₁ s₂ : State} (h : stateEquivBool s₁ s₂ = true) :
    StateEquiv s₁ s₂ := by
  simp only [stateEquivBool, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  rcases h with ⟨⟨hp, h12⟩, h21⟩
  refine ⟨hp, fun b => ⟨fun hb => List.contains_iff_mem.mp (h12 b hb),
                        fun hb => List.contains_iff_mem.mp (h21 b hb)⟩⟩

theorem StateEquiv.preserves_valid {L : Level} {s₁ s₂ : State}
    (heq : StateEquiv s₁ s₂) (hv : ValidState L s₁) : ValidState L s₂ := by
  rcases heq with ⟨hp, hboxes⟩
  rcases hv with ⟨hwp, hpb, hwb⟩
  refine ⟨hp ▸ hwp, ?_, ?_⟩
  · intro hmem
    exact hpb ((hboxes s₂.player).mpr (hp ▸ hmem) |> fun h => hp ▸ h)
  · intro b hb
    exact hwb b ((hboxes b).mpr hb)

theorem StateEquiv.preserves_solved {L : Level} {s₁ s₂ : State}
    (heq : StateEquiv s₁ s₂) (hsol : IsSolved L s₁) : IsSolved L s₂ :=
  fun b hb => hsol b ((heq.2 b).mpr hb)

theorem StateEquiv.preserves_step {L : Level} {s₁ s₂ s₁' : State}
    (heq : StateEquiv s₁ s₂) (hs : Step L s₁ s₁') :
    ∃ s₂', Step L s₂ s₂' ∧ StateEquiv s₁' s₂' := by
  rcases heq with ⟨hp, hboxes⟩
  cases hs with
  | walk d s hw hnb =>
    have hw2 : L.isWall (step s₂.player d) = false := hp ▸ hw
    have hnb2 : step s₂.player d ∉ s₂.boxes := fun hm => hnb ((hboxes _).mpr (hp ▸ hm))
    refine ⟨{ player := step s₂.player d, boxes := s₂.boxes }, Step.walk d s₂ hw2 hnb2, ?_⟩
    exact ⟨hp ▸ rfl, hboxes⟩
  | push d s hb hw hnb =>
    have hb2 : step s₂.player d ∈ s₂.boxes := hp ▸ (hboxes _).mp hb
    have hw2 : L.isWall (step (step s₂.player d) d) = false := hp ▸ hw
    have hnb2 : step (step s₂.player d) d ∉ s₂.boxes := fun hm => hnb ((hboxes _).mpr (hp ▸ hm))
    refine ⟨{ player := step s₂.player d
              boxes := moveBox s₂.boxes (step s₂.player d) (step (step s₂.player d) d) },
            Step.push d s₂ hb2 hw2 hnb2, ?_⟩
    refine ⟨hp ▸ rfl, fun x => ?_⟩
    rw [mem_moveBox hb, mem_moveBox hb2, hp]
    simp only [hboxes]

theorem StateEquiv.preserves_solvable {L : Level} {s₁ s₂ : State}
    (heq : StateEquiv s₁ s₂) (hsol : Solvable L s₁) : Solvable L s₂ := by
  rcases hsol with ⟨s₁_end, hr, hend⟩
  induction hr generalizing s₂ with
  | refl =>
    exact ⟨s₂, Reach.refl s₂, heq.preserves_solved hend⟩
  | step hs _ ih =>
    rcases heq.preserves_step hs with ⟨s₂', hs₂, heq'⟩
    rcases ih heq' hend with ⟨s₂_end, hr₂, hend₂⟩
    exact ⟨s₂_end, Reach.step hs₂ hr₂, hend₂⟩

theorem Step.preserves_playable {L : Level} {playable : List Pos}
    (hclosed : ClosedPlayable L playable) {s₁ s₂ : State}
    (hpl : s₁.player ∈ playable) (hbox : ∀ b ∈ s₁.boxes, b ∈ playable)
    (hs : Step L s₁ s₂) :
    s₂.player ∈ playable ∧ ∀ b ∈ s₂.boxes, b ∈ playable := by
  cases hs with
  | walk d s hw _ =>
    exact ⟨hclosed _ hpl d hw, hbox⟩
  | push d s hb hw _ =>
    refine ⟨hbox _ hb, fun b hmem => ?_⟩
    rw [mem_moveBox hb] at hmem
    rcases hmem with rfl | ⟨hb_old, _⟩
    · exact hclosed _ (hbox _ hb) d hw
    · exact hbox b hb_old

/--
Standalone, kernel-checkable unsolvability certificate verifier.
Checks that `visited` is a closed state-space invariant (modulo `StateEquiv`) starting from `s₀`:
1. `s₀` is represented in `visited`,
2. no state in `visited` is solved, and
3. every legal transition from a state in `visited` leads either to a verified Super-Freeze deadlock
   or back into `visited`.
-/
def checkUnsolvableCert (L : Level) (playable : List Pos) (s₀ : State) (visited : List State) : Bool :=
  let live := computeLiveSquares L playable
  visited.any (stateEquivBool s₀) &&
  visited.all (fun s => !isSolvedBool L s) &&
  visited.all (fun s =>
    Dir.all.all (fun d =>
      match execDir L s d with
      | none => true
      | some s' => isSuperFreezeDeadlockWithLive L playable live s' || visited.any (stateEquivBool s')))

theorem checkUnsolvableCert_sound {L : Level} {playable : List Pos} {s₀ : State} {visited : List State}
    (hv : ValidState L s₀) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s₀.player ∈ playable) (hbox : ∀ b ∈ s₀.boxes, b ∈ playable)
    (hcert : checkUnsolvableCert L playable s₀ visited = true) :
    ¬ Solvable L s₀ := by
  simp only [checkUnsolvableCert, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    Bool.not_eq_true'] at hcert
  rcases hcert with ⟨⟨⟨sv₀, hsv₀_mem, hsv₀_eq⟩, hnone_sol⟩, hclosed_vis⟩
  rintro ⟨s_end, hr, hend⟩
  suffices h : ∀ {s₁ s₂ : State}, Reach L s₁ s₂ →
      ∀ sv ∈ visited, StateEquiv s₁ sv →
      ValidState L s₁ → s₁.player ∈ playable → (∀ b ∈ s₁.boxes, b ∈ playable) →
      ¬ IsSolved L s₂ by
    exact h hr sv₀ hsv₀_mem (stateEquivBool_sound hsv₀_eq) hv hpl hbox hend
  intro s₁ s₂ hr₁₂
  induction hr₁₂ with
  | refl s₁ =>
    intro sv hsv_mem heq _ _ _ hsol
    have hsol_v := heq.preserves_solved hsol
    have hb_v : isSolvedBool L sv = false := hnone_sol sv hsv_mem
    have htrue : isSolvedBool L sv = true := by
      simp only [isSolvedBool, List.all_eq_true]
      exact hsol_v
    simp_all
  | @step s₁ s₂ s₃ hs hr₂₃ ih =>
    intro sv hsv_mem heq hv₁ hpl₁ hbox₁ hsol₃
    have hv₂ := hs.preserves_valid hv₁
    have hplay₂ := hs.preserves_playable hclosed hpl₁ hbox₁
    have hv_v := heq.preserves_valid hv₁
    rcases heq.preserves_step hs with ⟨sv', hsv_step, heq'⟩
    rcases step_implies_execDir hv_v hsv_step with ⟨d, hd⟩
    have hbranch := hclosed_vis sv hsv_mem d (Dir.mem_all d)
    simp only [hd, Bool.or_eq_true, List.any_eq_true] at hbranch
    rcases hbranch with hdead | ⟨sv₂, hsv₂_mem, heq₂_bool⟩
    · have hv_v' : ValidState L sv' := heq'.preserves_valid hv₂
      have hpl_v' : sv'.player ∈ playable := heq'.1 ▸ hplay₂.1
      have hbox_v' : ∀ b ∈ sv'.boxes, b ∈ playable := fun b hb => hplay₂.2 b ((heq'.2 b).mpr hb)
      have hnot : ¬ Solvable L sv' :=
        superFreezeDeadlockWithLive_sound hv_v' hp hclosed hpl_v' hbox_v' hdead
      have hsol_s₂ : Solvable L s₂ := ⟨s₃, hr₂₃, hsol₃⟩
      exact hnot (heq'.preserves_solvable hsol_s₂)
    · exact ih sv₂ hsv₂_mem (heq'.trans (stateEquivBool_sound heq₂_bool)) hv₂ hplay₂.1 hplay₂.2 hsol₃

/-- Result of the deadlock-pruned Sokoban BFS solver. -/
inductive SolveResult where
  | solved (moves : List Dir)
  | unsolvable (visited : List State)
  | outOfFuel
  deriving Repr, DecidableEq

/--
Deadlock-pruned Breadth-First Search (BFS) solver using `isSuperFreezeDeadlockWithLive`.
When returning `.unsolvable visited`, `visited` is an unsolvability certificate for `checkUnsolvableCert`.
-/
def solveBFS (L : Level) (playable : List Pos) (fuel : Nat) (s₀ : State) : SolveResult :=
  let live := computeLiveSquares L playable
  if isSolvedBool L s₀ then .solved []
  else if isSuperFreezeDeadlockWithLive L playable live s₀ then .unsolvable []
  else
    let rec go (f : Nat) (queue : List (State × List Dir)) (visited : List State) : SolveResult :=
      match f with
      | 0 => .outOfFuel
      | f' + 1 =>
        match queue with
        | [] => .unsolvable visited
        | (s, revPath) :: rest =>
          let stepDir (acc : List (State × List Dir) × List State × Option (List Dir)) (d : Dir) :=
            match acc.2.2 with
            | some sol => (acc.1, acc.2.1, some sol)
            | none =>
              match execDir L s d with
              | none => acc
              | some s' =>
                if isSolvedBool L s' then
                  (acc.1, acc.2.1, some (d :: revPath).reverse)
                else if acc.2.1.any (stateEquivBool s') then
                  acc
                else if isSuperFreezeDeadlockWithLive L playable live s' then
                  acc
                else
                  (acc.1 ++ [(s', d :: revPath)], s' :: acc.2.1, none)
          let (newItems, visited', found) := Dir.all.foldl stepDir ([], visited, none)
          match found with
          | some sol => .solved sol
          | none => go f' (rest ++ newItems) visited'
    go fuel [(s₀, [])] [s₀]

/--
Verified wrapper: checks any `.solved` solution via `applyMoves` and any `.unsolvable` certificate
via `checkUnsolvableCert`.
-/
def verifySolution (L : Level) (s₀ : State) (moves : List Dir) : Bool :=
  match applyMoves L s₀ moves with
  | none => false
  | some s' => isSolvedBool L s'

theorem verifySolution_sound {L : Level} {s₀ : State} {moves : List Dir}
    (h : verifySolution L s₀ moves = true) : Solvable L s₀ := by
  simp only [verifySolution] at h
  cases hm : applyMoves L s₀ moves with
  | none => simp [hm] at h
  | some s' =>
    simp [hm] at h
    exact solvable_of_applyMoves hm h

end Sokoban
