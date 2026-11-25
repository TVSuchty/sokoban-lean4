/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs
import Sokoban.Fixpoint
import Sokoban.DeadSquares
import Sokoban.Freeze

namespace Sokoban

/-!
# Verified PI-Corral Pruning & Corral Merging

A **corral** `(C, B)` is an enclosed region `C` of empty squares unreachable by the player,
bounded by walls and a set of border boxes `B ⊆ s₀.boxes`.
It is a **Dead-Square-Aware PI-Corral** (`IsPICorral`) if:
1. `B` contains at least one box not yet on a goal (`∃ b ∈ B, L.isGoal b = false`),
2. **I-Corral (stripping external boxes `s₀.boxes \ B`)**: every live push of a box `b ∈ B` from
   outside `C` (ignoring external boxes) lands *inside* `C`, and
3. **P-Corral (keeping all `s₀.boxes`)**: the player can currently walk to the pushing side of
   every such inward push avoiding all boxes `s₀.boxes`.

Because `IsPICorral` only requires `C` to be closed under `wall ∪ B`, it handles both **single
corrals** and **arbitrarily merged multi-room corrals** uniformly.

Our main theorem `piCorral_push_optimal` proves that whenever `IsPICorral` holds on a solvable
board, **at least one optimal solution starts with an immediate inward push into `C`** (after
pure walking)—so pruning all pushes outside `B` preserves both solvability and push-optimality.
-/

-- ============================================================================
-- 1. Push-Counted Reachability & Commutation
-- ============================================================================

/-- Multi-step Sokoban reachability counting the exact number of box pushes `k`. -/
inductive ReachPushes (L : Level) : State → State → Nat → Prop where
  | refl (s : State) : ReachPushes L s s 0
  | walk {s₁ s₂ : State} {d : Dir} {k : Nat}
      (hw : L.isWall (step s₁.player d) = false)
      (hb : step s₁.player d ∉ s₁.boxes)
      (hr : ReachPushes L { player := step s₁.player d, boxes := s₁.boxes } s₂ k) :
      ReachPushes L s₁ s₂ k
  | push {s₁ s₂ : State} {d : Dir} {k : Nat}
      (hb : step s₁.player d ∈ s₁.boxes)
      (hw : L.isWall (step (step s₁.player d) d) = false)
      (hnb : step (step s₁.player d) d ∉ s₁.boxes)
      (hr : ReachPushes L
        { player := step s₁.player d
          boxes := moveBox s₁.boxes (step s₁.player d) (step (step s₁.player d) d) } s₂ k) :
      ReachPushes L s₁ s₂ (k + 1)

theorem ReachPushes.toReach {L : Level} {s₁ s₂ : State} {k : Nat}
    (h : ReachPushes L s₁ s₂ k) : Reach L s₁ s₂ := by
  induction h with
  | refl => exact Reach.refl _
  | walk hw hb _ ih => exact Reach.step (Step.walk _ _ hw hb) ih
  | push hb hw hnb _ ih => exact Reach.step (Step.push _ _ hb hw hnb) ih

theorem Reach.exists_pushes {L : Level} {s₁ s₂ : State} (h : Reach L s₁ s₂) :
    ∃ k, ReachPushes L s₁ s₂ k := by
  induction h with
  | refl => exact ⟨0, ReachPushes.refl _⟩
  | step hs _ ih =>
    rcases ih with ⟨k, hr⟩
    cases hs with
    | walk d _ hw hb => exact ⟨k, ReachPushes.walk hw hb hr⟩
    | push d _ hb hw hnb => exact ⟨k + 1, ReachPushes.push hb hw hnb hr⟩

theorem ReachPushes.trans {L : Level} {s₁ s₂ s₃ : State} {k₁ k₂ : Nat}
    (h₁ : ReachPushes L s₁ s₂ k₁) (h₂ : ReachPushes L s₂ s₃ k₂) :
    ReachPushes L s₁ s₃ (k₁ + k₂) := by
  induction h₁ with
  | refl => simpa using h₂
  | walk hw hb _ ih => exact ReachPushes.walk hw hb (ih h₂)
  | push hb hw hnb _ ih =>
    have hsum := ReachPushes.push hb hw hnb (ih h₂)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum

theorem reachPushes_of_canWalkAvoiding {L : Level} {bs : List Pos} {p q : Pos}
    (h : CanWalkAvoiding L bs p q) :
    ReachPushes L { player := p, boxes := bs } { player := q, boxes := bs } 0 := by
  induction h with
  | refl => exact ReachPushes.refl _
  | step d hw hf _ ih => exact ReachPushes.walk hw hf ih

theorem moveBox_comm {bs : List Pos} {b₁ d₁ b₂ d₂ : Pos}
    (hb : b₁ ≠ b₂) (h₁ : d₁ ≠ b₂) (h₂ : d₂ ≠ b₁) :
    moveBox (moveBox bs b₁ d₁) b₂ d₂ = moveBox (moveBox bs b₂ d₂) b₁ d₁ := by
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [moveBox, List.map_cons] at ih ⊢
    by_cases ha1 : a = b₁
    · have h1a : (a == b₁) = true := beq_iff_eq.mpr ha1
      have h12 : (a == b₂) = false := beq_false_of_ne (ha1 ▸ hb)
      have hd12 : (d₁ == b₂) = false := beq_false_of_ne h₁
      rw [h1a, h12]
      simp only [↓reduceIte, Bool.false_eq_true]
      rw [hd12, h1a]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (d₁ :: ·) ih
    · by_cases ha2 : a = b₂
      · have h2a : (a == b₂) = true := beq_iff_eq.mpr ha2
        have h21 : (a == b₁) = false := beq_false_of_ne (ha2 ▸ hb.symm)
        have hd21 : (d₂ == b₁) = false := beq_false_of_ne h₂
        rw [h21, h2a]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h2a, hd21]
        simp only [↓reduceIte, Bool.false_eq_true]
        exact congrArg (d₂ :: ·) ih
      · have h1a : (a == b₁) = false := beq_false_of_ne ha1
        have h2a : (a == b₂) = false := beq_false_of_ne ha2
        rw [h1a, h2a]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h2a, h1a]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrArg (a :: ·) ih

-- ============================================================================
-- 2. Dead-Square-Aware PI-Corral Specification (Single & Merged)
-- ============================================================================

/--
A region `C` and border-box set `B` form a valid **Dead-Square-Aware PI-Corral** at state `s₀`
(covering both single corrals and arbitrarily merged multi-room corrals):
- `B ⊆ s₀.boxes`, `C` is empty and avoids walls, boxes, and `s₀.player`,
- `C` is enclosed by walls and `B` (`hC_encl`),
- `B` contains at least one non-goal box (`hUnsolved`),
- **I-Corral** (external boxes `s₀.boxes \ B` stripped): every live push of `b ∈ B` from
  outside `C` goes into `C` (`hICorral`), and
- **P-Corral** (all `s₀.boxes` kept): every such inward push is immediately executable by the
  player from `s₀.player` (`hPCorral`).
-/
structure IsPICorral (L : Level) (live : List Pos) (s₀ : State) (C B : List Pos) : Prop where
  hB_sub : ∀ b ∈ B, b ∈ s₀.boxes
  hC_nonwall : ∀ p ∈ C, L.isWall p = false
  hC_nobox : ∀ p ∈ C, p ∉ s₀.boxes
  hP_notC : s₀.player ∉ C
  hC_encl : ∀ p ∈ C, ∀ d : Dir, L.isWall (step p d) = false → step p d ∉ B → step p d ∈ C
  hUnsolved : ∃ b ∈ B, L.isGoal b = false
  hICorral : ∀ b ∈ B, ∀ d : Dir,
    L.isWall (step b d.opp) = false → step b d.opp ∉ B → step b d.opp ∉ C →
    L.isWall (step b d) = false → step b d ∉ B → step b d ∈ live →
    step b d ∈ C
  hPCorral : ∀ b ∈ B, ∀ d : Dir,
    L.isWall (step b d.opp) = false → step b d.opp ∉ B → step b d.opp ∉ C →
    L.isWall (step b d) = false → step b d ∉ B → step b d ∈ live →
    CanWalkAvoiding L s₀.boxes s₀.player (step b d.opp)

-- ============================================================================
-- 3. Prefix/Suffix Splitting & Shifted Replay
-- ============================================================================

/-- A push-counted trace that never pushes a box in `B` and never enters `C`. -/
inductive ReachAvoidingBC (L : Level) (B C : List Pos) : State → State → Nat → Prop where
  | refl (s : State) : ReachAvoidingBC L B C s s 0
  | walk {s₁ s₂ : State} {d : Dir} {k : Nat}
      (hw : L.isWall (step s₁.player d) = false)
      (hb : step s₁.player d ∉ s₁.boxes)
      (hc : step s₁.player d ∉ C)
      (hr : ReachAvoidingBC L B C { player := step s₁.player d, boxes := s₁.boxes } s₂ k) :
      ReachAvoidingBC L B C s₁ s₂ k
  | push {s₁ s₂ : State} {d : Dir} {k : Nat}
      (hb : step s₁.player d ∈ s₁.boxes)
      (hb_notB : step s₁.player d ∉ B)
      (hw : L.isWall (step (step s₁.player d) d) = false)
      (hnb : step (step s₁.player d) d ∉ s₁.boxes)
      (hdest_notC : step (step s₁.player d) d ∉ C)
      (hp_notC : step s₁.player d ∉ C)
      (hr : ReachAvoidingBC L B C
        { player := step s₁.player d
          boxes := moveBox s₁.boxes (step s₁.player d) (step (step s₁.player d) d) } s₂ k) :
      ReachAvoidingBC L B C s₁ s₂ (k + 1)

private theorem encl_step_out_not_in_C {L : Level} {B C : List Pos}
    (hC_encl : ∀ p ∈ C, ∀ d : Dir, L.isWall (step p d) = false → step p d ∉ B → step p d ∈ C)
    {p : Pos} (d : Dir) (hp : p ∉ C) (hwp : L.isWall p = false) (hbp : p ∉ B) :
    step p d ∉ C := by
  intro hc
  have hback := hC_encl (step p d) hc d.opp (by rw [step_opp]; exact hwp) (by rw [step_opp]; exact hbp)
  rw [step_opp] at hback
  exact hp hback

private theorem canWalkAvoiding_shifted {L : Level} {bs B C : List Pos}
    (hC_encl : ∀ p ∈ C, ∀ d : Dir, L.isWall (step p d) = false → step p d ∉ B → step p d ∈ C)
    (hB_sub : ∀ b ∈ B, b ∈ bs)
    {b₀ dest₀ p₁ p₂ : Pos} (hb₀ : b₀ ∈ bs) (hdestC : dest₀ ∈ C)
    (hw₁ : L.isWall p₁ = false) (hp₁B : p₁ ∉ B) (hp₁ : p₁ ∉ C)
    (hwalk : CanWalkAvoiding L bs p₁ p₂) :
    CanWalkAvoiding L (moveBox bs b₀ dest₀) p₁ p₂ := by
  induction hwalk with
  | refl => exact CanWalkAvoiding.refl _
  | @step p q d hwd hbd _ ih =>
    have hstep_notC : step p d ∉ C :=
      encl_step_out_not_in_C hC_encl d hp₁ hw₁ hp₁B
    have hstep_notB : step p d ∉ B := fun hm => hbd (hB_sub (step p d) hm)
    have hnot_moved : step p d ∉ moveBox bs b₀ dest₀ := by
      rw [mem_moveBox hb₀]
      rintro (heq | ⟨hm, _⟩)
      · exact hstep_notC (heq ▸ hdestC)
      · exact hbd hm
    exact CanWalkAvoiding.step d hwd hnot_moved (ih hwd hstep_notB hstep_notC)

private theorem split_first_push_in_B {L : Level} {playable : List Pos}
    (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    {s₀ s_end : State} {C B : List Pos} {k : Nat}
    (hpi : IsPICorral L (computeLiveSquares L playable) s₀ C B)
    (hsol : IsSolved L s_end)
    (hr : ReachPushes L s₀ s_end k)
    (hv₀ : ValidState L s₀) (hpl₀ : s₀.player ∈ playable) (hbox₀ : ∀ b ∈ s₀.boxes, b ∈ playable) :
    ∃ s_pre : State, ∃ d : Dir, ∃ k₁ k₂ : Nat,
      k = k₁ + 1 + k₂ ∧
      ReachAvoidingBC L B C s₀ s_pre k₁ ∧
      ValidState L s_pre ∧
      step s_pre.player d ∈ s_pre.boxes ∧
      step s_pre.player d ∈ B ∧
      step (step s_pre.player d) d ∈ C ∧
      L.isWall (step (step s_pre.player d) d) = false ∧
      step (step s_pre.player d) d ∉ s_pre.boxes ∧
      s_pre.player ∉ C ∧
      CanWalkAvoiding L s₀.boxes s₀.player s_pre.player ∧
      ReachPushes L
        { player := step s_pre.player d
          boxes := moveBox s_pre.boxes (step s_pre.player d) (step (step s_pre.player d) d) }
        s_end k₂ := by
  suffices h : ∀ {s₁ s_end' : State} {k' : Nat}, ReachPushes L s₁ s_end' k' →
      IsSolved L s_end' →
      ValidState L s₁ → s₁.player ∈ playable → (∀ b ∈ s₁.boxes, b ∈ playable) →
      s₁.player ∉ C → (∀ p ∈ C, p ∉ s₁.boxes) → (∀ b ∈ B, b ∈ s₁.boxes) →
      ∃ s_pre : State, ∃ d : Dir, ∃ k₁ k₂ : Nat,
        k' = k₁ + 1 + k₂ ∧
        ReachAvoidingBC L B C s₁ s_pre k₁ ∧
        ValidState L s_pre ∧
        step s_pre.player d ∈ s_pre.boxes ∧
        step s_pre.player d ∈ B ∧
        step (step s_pre.player d) d ∈ C ∧
        L.isWall (step (step s_pre.player d) d) = false ∧
        step (step s_pre.player d) d ∉ s_pre.boxes ∧
        s_pre.player ∉ C ∧
        CanWalkAvoiding L s₀.boxes s₀.player s_pre.player ∧
        ReachPushes L
          { player := step s_pre.player d
            boxes := moveBox s_pre.boxes (step s_pre.player d) (step (step s_pre.player d) d) }
          s_end' k₂ from
    h hr hsol hv₀ hpl₀ hbox₀ hpi.hP_notC hpi.hC_nobox hpi.hB_sub
  intro s₁ s_end' k' hr₁
  induction hr₁ with
  | refl s₁ =>
    intro hsol' _ _ _ _ _ hB_in
    rcases hpi.hUnsolved with ⟨b, hbB, hng⟩
    have hg := hsol' b (hB_in b hbB)
    simp_all
  | @walk s₁ s₂ d k_w hw hb hr_rest ih =>
    intro hsol' hv₁ hpl₁ hbox₁ hp_notC hC_nobox hB_in
    have hs : Step L s₁ { player := step s₁.player d, boxes := s₁.boxes } := Step.walk d s₁ hw hb
    have hv₂ := hs.preserves_valid hv₁
    have hpl₂ := hclosed s₁.player hpl₁ d hw
    have hp₂_notC : step s₁.player d ∉ C :=
      encl_step_out_not_in_C hpi.hC_encl d hp_notC hv₁.1 (fun hm => hv₁.2.1 (hB_in s₁.player hm))
    rcases ih hsol' hv₂ hpl₂ hbox₁ hp₂_notC hC_nobox hB_in with
      ⟨s_pre, d', k₁, k₂, hkeq, hpref, hv_pre, hbin, hbB, hdestC, hwd, hnbd, hpre_notC, hwalk, hsuf⟩
    exact ⟨s_pre, d', k₁, k₂, hkeq, ReachAvoidingBC.walk hw hb hp₂_notC hpref,
      hv_pre, hbin, hbB, hdestC, hwd, hnbd, hpre_notC, hwalk, hsuf⟩
  | @push s₁ s₂ d k_p hb hw hnb hr_rest ih =>
    intro hsol' hv₁ hpl₁ hbox₁ hp_notC hC_nobox hB_in
    let b₀ := step s₁.player d
    let dest := step b₀ d
    have hs : Step L s₁ { player := b₀, boxes := moveBox s₁.boxes b₀ dest } :=
      Step.push d s₁ hb hw hnb
    have hv₂ := hs.preserves_valid hv₁
    have hpl₂ : b₀ ∈ playable := hbox₁ b₀ hb
    have hbox₂ : ∀ b ∈ moveBox s₁.boxes b₀ dest, b ∈ playable := by
      intro b hmem
      rw [mem_moveBox hb] at hmem
      rcases hmem with rfl | ⟨hb_old, _⟩
      · exact hclosed b₀ hpl₂ d hw
      · exact hbox₁ b hb_old
    by_cases hb₀B : b₀ ∈ B
    · have hdest_play : dest ∈ playable := hclosed b₀ hpl₂ d hw
      have hdest_in : dest ∈ moveBox s₁.boxes b₀ dest := (mem_moveBox hb).mpr (.inl rfl)
      have hlive : dest ∈ computeLiveSquares L playable := by
        rcases reach_tracks_box hv₂ hr_rest.toReach dest hdest_in with ⟨g, hg_in, hbr⟩
        exact singleBoxReach_goal_mem_liveSquares hp hclosed hdest_play hbr (hsol' g hg_in)
      have hpushPos_notB : s₁.player ∉ B := fun hm => hv₁.2.1 (hB_in s₁.player hm)
      have hb₀_opp : step b₀ d.opp = s₁.player := step_opp s₁.player d
      have hdest_notB : dest ∉ B := fun hm => hnb (hB_in dest hm)
      have hdestC : dest ∈ C :=
        hpi.hICorral b₀ hb₀B d (by rw [hb₀_opp]; exact hv₁.1) (by rw [hb₀_opp]; exact hpushPos_notB)
          (by rw [hb₀_opp]; exact hp_notC) hw hdest_notB hlive
      have hwalk : CanWalkAvoiding L s₀.boxes s₀.player s₁.player := by
        rw [← hb₀_opp]
        exact hpi.hPCorral b₀ hb₀B d (by rw [hb₀_opp]; exact hv₁.1) (by rw [hb₀_opp]; exact hpushPos_notB)
          (by rw [hb₀_opp]; exact hp_notC) hw hdest_notB hlive
      exact ⟨s₁, d, 0, k_p, by omega, ReachAvoidingBC.refl s₁, hv₁, hb, hb₀B, hdestC, hw, hnb,
        hp_notC, hwalk, hr_rest⟩
    · have hb₀_notC : b₀ ∉ C := fun hm => hC_nobox b₀ hm hb
      have hdest_notC : dest ∉ C :=
        encl_step_out_not_in_C hpi.hC_encl d hb₀_notC (hv₁.2.2.1 b₀ hb) hb₀B
      have hC_nobox₂ : ∀ p ∈ C, p ∉ moveBox s₁.boxes b₀ dest := by
        intro p hpC hmem
        rw [mem_moveBox hb] at hmem
        rcases hmem with rfl | ⟨hp_old, _⟩
        · exact hdest_notC hpC
        · exact hC_nobox p hpC hp_old
      have hB_in₂ : ∀ b ∈ B, b ∈ moveBox s₁.boxes b₀ dest := by
        intro b hbB
        have hne : b ≠ b₀ := fun heq => hb₀B (heq ▸ hbB)
        exact (mem_moveBox hb).mpr (.inr ⟨hB_in b hbB, hne⟩)
      rcases ih hsol' hv₂ hpl₂ hbox₂ hb₀_notC hC_nobox₂ hB_in₂ with
        ⟨s_pre, d', k₁, k₂, hkeq, hpref, hv_pre, hbin, hbB, hdestC, hwd, hnbd, hpre_notC, hwalk, hsuf⟩
      exact ⟨s_pre, d', k₁ + 1, k₂, by omega,
        ReachAvoidingBC.push hb hb₀B hw hnb hdest_notC hb₀_notC hpref,
        hv_pre, hbin, hbB, hdestC, hwd, hnbd, hpre_notC, hwalk, hsuf⟩

private theorem replay_avoiding_shifted {L : Level} {B C : List Pos}
    {s₁ s₂ : State} {k : Nat} {b₀ dest₀ : Pos}
    (hb₀B : b₀ ∈ B) (hdest₀C : dest₀ ∈ C)
    (hr : ReachAvoidingBC L B C s₁ s₂ k)
    (hb₀_in : b₀ ∈ s₁.boxes) (hdest₀_out : dest₀ ∉ s₁.boxes)
    (hC_nobox : ∀ p ∈ C, p ∉ s₁.boxes) :
    ReachPushes L { player := s₁.player, boxes := moveBox s₁.boxes b₀ dest₀ }
                 { player := s₂.player, boxes := moveBox s₂.boxes b₀ dest₀ } k := by
  induction hr with
  | refl => exact ReachPushes.refl _
  | @walk s₁ s₂ d k_w hw hb hc _ ih =>
    have hb' : step s₁.player d ∉ moveBox s₁.boxes b₀ dest₀ := by
      rw [mem_moveBox hb₀_in]
      rintro (heq | ⟨hm, _⟩)
      · exact hc (heq ▸ hdest₀C)
      · exact hb hm
    exact ReachPushes.walk hw hb' (ih hb₀_in hdest₀_out hC_nobox)
  | @push s₁ s₂ d k_p hb hb_notB hw hnb hdest_notC hp_notC _ ih =>
    let b' := step s₁.player d
    let dest' := step b' d
    have hne_b : b' ≠ b₀ := fun heq => hb_notB (by dsimp only [b'] at heq; rw [heq]; exact hb₀B)
    have hne_dest0 : dest₀ ≠ b' := fun heq => hp_notC (by dsimp only [b'] at heq; rw [← heq]; exact hdest₀C)
    have hne_dest' : dest' ≠ b₀ := fun heq => hnb (by dsimp only [dest', b'] at heq; rw [heq]; exact hb₀_in)
    have hb_shifted : b' ∈ moveBox s₁.boxes b₀ dest₀ :=
      (mem_moveBox hb₀_in).mpr (.inr ⟨hb, hne_b⟩)
    have hnb_shifted : dest' ∉ moveBox s₁.boxes b₀ dest₀ := by
      rw [mem_moveBox hb₀_in]
      rintro (heq | ⟨hm, _⟩)
      · exact hdest_notC (by dsimp only [dest', b'] at heq; rw [heq]; exact hdest₀C)
      · exact hnb hm
    have hb₀_in₂ : b₀ ∈ moveBox s₁.boxes b' dest' :=
      (mem_moveBox hb).mpr (.inr ⟨hb₀_in, hne_b.symm⟩)
    have hdest₀_out₂ : dest₀ ∉ moveBox s₁.boxes b' dest' := by
      rw [mem_moveBox hb]
      rintro (heq | ⟨hm, _⟩)
      · exact hdest_notC (by dsimp only [dest', b'] at heq; rw [← heq]; exact hdest₀C)
      · exact hdest₀_out hm
    have hC_nobox₂ : ∀ p ∈ C, p ∉ moveBox s₁.boxes b' dest' := by
      intro p hpC hm
      rw [mem_moveBox hb] at hm
      rcases hm with rfl | ⟨hm_old, _⟩
      · exact hdest_notC hpC
      · exact hC_nobox p hpC hm_old
    have ih' := ih hb₀_in₂ hdest₀_out₂ hC_nobox₂
    rw [moveBox_comm hne_b hne_dest' hne_dest0] at ih'
    exact ReachPushes.push hb_shifted hw hnb_shifted ih'

-- ============================================================================
-- 4. Main PI-Corral Theorems (Push-Optimality, Solvability, Deadlock Soundness)
-- ============================================================================

/--
**PI-Corral Push-Optimality Theorem (Single & Merged Corrals):**
If `(C, B)` is a valid Dead-Square-Aware PI-Corral at `s₀`, and `s₀` can be solved in `k` pushes,
then `k = k' + 1` and there is an immediate inward push of some `b ∈ B` in direction `d` into `C`
(with player walkability from `s₀.player` to `step b d.opp`) whose resulting state can be solved in
**strictly fewer** (`k'`) pushes!
-/
theorem piCorral_push_optimal {L : Level} {playable : List Pos}
    {s₀ s_end : State} {C B : List Pos} {k : Nat}
    (hv : ValidState L s₀) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s₀.player ∈ playable) (hbox : ∀ b ∈ s₀.boxes, b ∈ playable)
    (hpi : IsPICorral L (computeLiveSquares L playable) s₀ C B)
    (hr : ReachPushes L s₀ s_end k) (hsol : IsSolved L s_end) :
    ∃ b ∈ B, ∃ d : Dir, ∃ k' : Nat,
      k = k' + 1 ∧
      step b d ∈ C ∧
      CanWalkAvoiding L s₀.boxes s₀.player (step b d.opp) ∧
      L.isWall (step b d) = false ∧
      step b d ∉ s₀.boxes ∧
      ReachPushes L { player := b, boxes := moveBox s₀.boxes b (step b d) } s_end k' := by
  rcases split_first_push_in_B hp hclosed hpi hsol hr hv hpl hbox with
    ⟨s_pre, d, k₁, k₂, hkeq, hpref, hv_pre, hbin_pre, hb₀B, hdestC, hwd, hnbd, hpre_notC, hwalk, hsuf⟩
  let b₀ := step s_pre.player d
  let dest := step b₀ d
  have hb₀_in₀ : b₀ ∈ s₀.boxes := hpi.hB_sub b₀ hb₀B
  have hdest_not₀ : dest ∉ s₀.boxes := hpi.hC_nobox dest hdestC
  have hb₀_ne_dest : b₀ ≠ dest := (step_ne b₀ d).symm
  have hopp : step b₀ d.opp = s_pre.player := step_opp s_pre.player d
  have hwalk_opp : CanWalkAvoiding L s₀.boxes s₀.player (step b₀ d.opp) := by
    rw [hopp]; exact hwalk
  have hstep1 : ReachPushes L
      { player := b₀, boxes := moveBox s₀.boxes b₀ dest }
      { player := s_pre.player, boxes := moveBox s₀.boxes b₀ dest } 0 := by
    have hw_pre : L.isWall (step b₀ d.opp) = false := by rw [hopp]; exact hv_pre.1
    have hnb_pre : step b₀ d.opp ∉ moveBox s₀.boxes b₀ dest := by
      rw [hopp, mem_moveBox hb₀_in₀]
      rintro (heq | ⟨hm, _⟩)
      · exact hpre_notC (heq ▸ hdestC)
      · exact (canWalkAvoiding_end_valid hv.1 hv.2.1 hwalk).2 hm
    have hwalk1 := @ReachPushes.walk L
      { player := b₀, boxes := moveBox s₀.boxes b₀ dest }
      { player := step b₀ d.opp, boxes := moveBox s₀.boxes b₀ dest }
      d.opp 0 hw_pre hnb_pre (ReachPushes.refl _)
    simpa [hopp] using hwalk1
  have hwalk_rev : CanWalkAvoiding L (moveBox s₀.boxes b₀ dest) s_pre.player s₀.player := by
    have hsymm := canWalkAvoiding_symm hv.1 hv.2.1 hwalk
    have hpre_notB : s_pre.player ∉ B := fun hm =>
      (canWalkAvoiding_end_valid hv.1 hv.2.1 hwalk).2 (hpi.hB_sub s_pre.player hm)
    exact canWalkAvoiding_shifted hpi.hC_encl hpi.hB_sub hb₀_in₀ hdestC hv_pre.1 hpre_notB hpre_notC hsymm
  have hstep2 : ReachPushes L
      { player := s_pre.player, boxes := moveBox s₀.boxes b₀ dest }
      { player := s₀.player, boxes := moveBox s₀.boxes b₀ dest } 0 :=
    reachPushes_of_canWalkAvoiding hwalk_rev
  have hstep3 : ReachPushes L
      { player := s₀.player, boxes := moveBox s₀.boxes b₀ dest }
      { player := s_pre.player, boxes := moveBox s_pre.boxes b₀ dest } k₁ :=
    replay_avoiding_shifted hb₀B hdestC hpref hb₀_in₀ hdest_not₀ hpi.hC_nobox
  have hstep4 : ReachPushes L
      { player := s_pre.player, boxes := moveBox s_pre.boxes b₀ dest }
      { player := b₀, boxes := moveBox s_pre.boxes b₀ dest } 0 := by
    have hwb₀ : L.isWall b₀ = false := hv_pre.2.2.1 b₀ hbin_pre
    have hnb_b₀ : b₀ ∉ moveBox s_pre.boxes b₀ dest := moveBox_not_mem_old hb₀_ne_dest
    exact ReachPushes.walk hwb₀ hnb_b₀ (ReachPushes.refl _)
  have hcombined := ((hstep1.trans hstep2).trans hstep3).trans (hstep4.trans hsuf)
  have hzero : 0 + 0 + k₁ + (0 + k₂) = k₁ + k₂ := by omega
  rw [hzero] at hcombined
  exact ⟨b₀, hb₀B, d, k₁ + k₂, by omega, hdestC, hwalk_opp, hwd, hdest_not₀, hcombined⟩

/-- Solvability preservation corollary of `piCorral_push_optimal`. -/
theorem piCorral_solvable_preservation {L : Level} {playable : List Pos}
    {s₀ : State} {C B : List Pos}
    (hv : ValidState L s₀) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s₀.player ∈ playable) (hbox : ∀ b ∈ s₀.boxes, b ∈ playable)
    (hpi : IsPICorral L (computeLiveSquares L playable) s₀ C B)
    (hsolv : Solvable L s₀) :
    ∃ b ∈ B, ∃ d : Dir,
      step b d ∈ C ∧
      CanWalkAvoiding L s₀.boxes s₀.player (step b d.opp) ∧
      L.isWall (step b d) = false ∧
      step b d ∉ s₀.boxes ∧
      Solvable L { player := b, boxes := moveBox s₀.boxes b (step b d) } := by
  rcases hsolv with ⟨s_end, hr, hsol⟩
  rcases hr.exists_pushes with ⟨k, hrp⟩
  rcases piCorral_push_optimal hv hp hclosed hpl hbox hpi hrp hsol with
    ⟨b, hbB, d, k', _, hdestC, hwalk, hwd, hnbd, hr'⟩
  exact ⟨b, hbB, d, hdestC, hwalk, hwd, hnbd, ⟨s_end, hr'.toReach, hsol⟩⟩

/--
Dynamic PI-Corral deadlock theorem:
If every legal inward push of `IsPICorral` leads to an unsolvable state, `s₀` itself is unsolvable.
-/
theorem piCorral_deadlock_sound {L : Level} {playable : List Pos}
    {s₀ : State} {C B : List Pos}
    (hv : ValidState L s₀) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s₀.player ∈ playable) (hbox : ∀ b ∈ s₀.boxes, b ∈ playable)
    (hpi : IsPICorral L (computeLiveSquares L playable) s₀ C B)
    (hall_dead : ∀ b ∈ B, ∀ d : Dir,
      step b d ∈ C →
      CanWalkAvoiding L s₀.boxes s₀.player (step b d.opp) →
      L.isWall (step b d) = false →
      step b d ∉ s₀.boxes →
      ¬ Solvable L { player := b, boxes := moveBox s₀.boxes b (step b d) }) :
    ¬ Solvable L s₀ := by
  intro hsolv
  rcases piCorral_solvable_preservation hv hp hclosed hpl hbox hpi hsolv with
    ⟨b, hbB, d, hdestC, hwalk, hwd, hnbd, hsolv'⟩
  exact hall_dead b hbB d hdestC hwalk hwd hnbd hsolv'

-- ============================================================================
-- 5. Executable PI-Corral Checker & Merged Corral Finder
-- ============================================================================

/-- Executable checker for `IsPICorral` (strips `s₀.boxes \ B` in I-check, keeps `s₀.boxes` in P-check). -/
def isPICorralBool (L : Level) (playable live : List Pos) (s₀ : State) (C B : List Pos) : Bool :=
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
    if !L.isWall pushPos && !B.contains pushPos && !C.contains pushPos &&
       !L.isWall dest && !B.contains dest && live.contains dest then
      C.contains dest && walkable.contains pushPos
    else true))

theorem isPICorralBool_sound {L : Level} {playable live : List Pos} {s₀ : State} {C B : List Pos}
    (h : isPICorralBool L playable live s₀ C B = true) :
    IsPICorral L live s₀ C B := by
  simp only [isPICorralBool, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.any_eq_true, Bool.or_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hB⟩, hC⟩, hpC⟩, hEncl⟩, hUnsolv⟩, hIP⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb; exact List.contains_iff_mem.mp (hB b hb)
  · intro p hp; exact (hC p hp).1
  · intro p hp hm
    have := (hC p hp).2
    have hct := List.contains_iff_mem.mpr hm
    simp_all
  · intro hm
    have hct := List.contains_iff_mem.mpr hm
    simp_all
  · intro p hp d hw hb
    have hd := hEncl p hp d (Dir.mem_all d)
    rcases hd with (hw' | hb') | hc'
    · simp_all
    · exact False.elim (hb (List.contains_iff_mem.mp hb'))
    · exact List.contains_iff_mem.mp hc'
  · exact hUnsolv
  · intro b hb d hw1 hb1 hc1 hw2 hb2 hlive
    have hbd := hIP b hb d (Dir.mem_all d)
    have h1 : B.contains (step b d.opp) = false := by
      cases hc : B.contains (step b d.opp)
      · rfl
      · exact False.elim (hb1 (List.contains_iff_mem.mp hc))
    have h2 : C.contains (step b d.opp) = false := by
      cases hc : C.contains (step b d.opp)
      · rfl
      · exact False.elim (hc1 (List.contains_iff_mem.mp hc))
    have h3 : B.contains (step b d) = false := by
      cases hc : B.contains (step b d)
      · rfl
      · exact False.elim (hb2 (List.contains_iff_mem.mp hc))
    have h4 : live.contains (step b d) = true := List.contains_iff_mem.mpr hlive
    rw [hw1, h1, h2, hw2, h3, h4] at hbd
    simp only [and_self, ↓reduceIte, Bool.and_eq_true] at hbd
    exact List.contains_iff_mem.mp hbd.1
  · intro b hb d hw1 hb1 hc1 hw2 hb2 hlive
    have hbd := hIP b hb d (Dir.mem_all d)
    have h1 : B.contains (step b d.opp) = false := by
      cases hc : B.contains (step b d.opp)
      · rfl
      · exact False.elim (hb1 (List.contains_iff_mem.mp hc))
    have h2 : C.contains (step b d.opp) = false := by
      cases hc : C.contains (step b d.opp)
      · rfl
      · exact False.elim (hc1 (List.contains_iff_mem.mp hc))
    have h3 : B.contains (step b d) = false := by
      cases hc : B.contains (step b d)
      · rfl
      · exact False.elim (hb2 (List.contains_iff_mem.mp hc))
    have h4 : live.contains (step b d) = true := List.contains_iff_mem.mpr hlive
    rw [hw1, h1, h2, hw2, h3, h4] at hbd
    simp only [and_self, ↓reduceIte, Bool.and_eq_true] at hbd
    exact mem_computeWalkable_canWalkAvoiding (List.contains_iff_mem.mp hbd.2)

/-- List all currently executable inward pushes `(b, d)` of a PI-Corral `(C, B)`. -/
def piCorralInwardPushes (L : Level) (playable live : List Pos) (s₀ : State)
    (C B : List Pos) : List (Pos × Dir) :=
  let walkable := computeWalkable L playable s₀.boxes s₀.player
  B.foldl (fun acc b =>
    acc ++ (Dir.all.filter (fun d =>
      let pushPos := step b d.opp
      let dest := step b d
      C.contains dest && live.contains dest &&
      !L.isWall dest && !s₀.boxes.contains dest && walkable.contains pushPos)).map (fun d => (b, d))) []

/-- Partition unreachable playable cells into connected corral components `(C, adjBoxes)`. -/
def findCorralComponents (L : Level) (playable : List Pos) (s₀ : State) :
    List (List Pos × List Pos) :=
  let walk := computeWalkable L playable s₀.boxes s₀.player
  let unreached := playable.filter (fun p => !s₀.boxes.contains p && !walk.contains p)
  let uniqBoxes := dedupPos s₀.boxes
  let rec go (fuel : Nat) (rem : List Pos) (seen : List Pos)
      (acc : List (List Pos × List Pos)) : List (List Pos × List Pos) :=
    match fuel, rem with
    | 0, _ => acc
    | _, [] => acc
    | f + 1, p :: rest =>
      if seen.contains p then go f rest seen acc
      else
        let comp := computeWalkable L playable s₀.boxes p
        let adjB := uniqBoxes.filter (fun b => Dir.all.any (fun d => comp.contains (step b d)))
        go f rest (seen ++ comp) (acc ++ [(comp, adjB)])
  go unreached.length unreached [] []

/--
Search for a single or merged Dead-Square-Aware PI-Corral `(C, B)` at state `s₀`.
Starts from each corral component and greedily merges any neighboring component reached by a
live push of a current border box `b ∈ B`.
-/
def findPICorral (L : Level) (playable live : List Pos) (s₀ : State) :
    Option (List Pos × List Pos) :=
  let comps := findCorralComponents L playable s₀
  let rec expand (fuel : Nat) (C B : List Pos) : Option (List Pos × List Pos) :=
    if isPICorralBool L playable live s₀ C B then some (C, B)
    else match fuel with
    | 0 => none
    | f + 1 =>
      let neighbor? := comps.find? (fun (C', _) =>
        !(C'.all (fun p => C.contains p)) &&
        B.any (fun b => Dir.all.any (fun d =>
          let pushPos := step b d.opp
          let dest := step b d
          !L.isWall pushPos && !B.contains pushPos && !C.contains pushPos &&
          !L.isWall dest && !B.contains dest && live.contains dest && C'.contains dest)))
      match neighbor? with
      | none => none
      | some (C', B') => expand f (dedupPos (C ++ C')) (dedupPos (B ++ B'))
  comps.findSome? (fun (C₀, B₀) => expand comps.length C₀ B₀)

end Sokoban
