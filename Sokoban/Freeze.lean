/-
Copyright 2026 Niclas Schwalbe
Licensed under the Apache License, Version 2.0.
-/
import Sokoban.Defs
import Sokoban.Fixpoint
import Sokoban.DeadSquares

namespace Sokoban

/-- Player walkability from `p` to `q` avoiding walls and a set `F` of frozen boxes. -/
inductive CanWalkAvoiding (L : Level) (F : List Pos) : Pos → Pos → Prop where
  | refl (p : Pos) : CanWalkAvoiding L F p p
  | step {p q : Pos} (d : Dir) :
      L.isWall (step p d) = false →
      step p d ∉ F →
      CanWalkAvoiding L F (step p d) q →
      CanWalkAvoiding L F p q

theorem CanWalkAvoiding.trans {L : Level} {F : List Pos} {p q r : Pos}
    (h₁ : CanWalkAvoiding L F p q) (h₂ : CanWalkAvoiding L F q r) :
    CanWalkAvoiding L F p r := by
  induction h₁ with
  | refl => exact h₂
  | step d hw hf _ ih => exact CanWalkAvoiding.step d hw hf (ih h₂)

theorem canWalkAvoiding_snoc {L : Level} {F : List Pos} {p q : Pos} (d : Dir)
    (h : CanWalkAvoiding L F p q)
    (hw : L.isWall (step q d) = false) (hf : step q d ∉ F) :
    CanWalkAvoiding L F p (step q d) :=
  h.trans (CanWalkAvoiding.step d hw hf (CanWalkAvoiding.refl _))

theorem canWalkAvoiding_symm {L : Level} {F : List Pos} {p q : Pos}
    (hw : L.isWall p = false) (hf : p ∉ F)
    (h : CanWalkAvoiding L F p q) : CanWalkAvoiding L F q p := by
  induction h with
  | refl => exact CanWalkAvoiding.refl _
  | @step p' q' d hwd hfd _ ih =>
    have ih' := ih hwd hfd
    have hstep : step (step p' d) d.opp = p' := step_opp p' d
    have hw' : L.isWall (step (step p' d) d.opp) = false := by rw [hstep]; exact hw
    have hf' : step (step p' d) d.opp ∉ F := by rw [hstep]; exact hf
    have hback : CanWalkAvoiding L F (step p' d) p' := by
      have h1 := CanWalkAvoiding.step d.opp hw' hf' (CanWalkAvoiding.refl _)
      rw [hstep] at h1
      exact h1
    exact ih'.trans hback

theorem canWalkAvoiding_end_valid {L : Level} {F : List Pos} {p q : Pos}
    (hw : L.isWall p = false) (hf : p ∉ F)
    (h : CanWalkAvoiding L F p q) : L.isWall q = false ∧ q ∉ F := by
  induction h with
  | refl => exact ⟨hw, hf⟩
  | step _ hwd hfd _ ih => exact ih hwd hfd

/-- One BFS expansion step for player walkability avoiding walls and `F`. -/
def walkStep (L : Level) (playable F reach : List Pos) : List Pos :=
  playable.filter (fun p =>
    reach.contains p ||
    (!L.isWall p && !F.contains p && Dir.all.any (fun d => reach.contains (step p d))))

/-- All positions in `playable` reachable by the player from `start` avoiding walls and `F`. -/
def computeWalkable (L : Level) (playable F : List Pos) (start : Pos) : List Pos :=
  let init := if playable.contains start && !L.isWall start && !F.contains start then [start] else []
  iterFixedUp (walkStep L playable F) playable.length init

private theorem walkStep_props {L : Level} {playable F : List Pos}
    (hp : playable.Nodup) :
    ∀ ys, SubPos ys playable →
      SubPos ys (walkStep L playable F ys) ∧
      SubPos (walkStep L playable F ys) playable ∧
      (walkStep L playable F ys).Nodup := by
  intro ys hsub
  refine ⟨?_, ?_, nodup_filter hp⟩
  · intro x hx
    simp only [walkStep, List.mem_filter, Bool.or_eq_true]
    exact ⟨hsub x hx, .inl (List.contains_iff_mem.mpr hx)⟩
  · intro x hx
    simp only [walkStep, List.mem_filter] at hx
    exact hx.1

theorem canWalkAvoiding_mem_computeWalkable {L : Level} {playable F : List Pos}
    (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    {start q : Pos} (hstart : start ∈ playable) (hw0 : L.isWall start = false) (hf0 : start ∉ F)
    (hwalk : CanWalkAvoiding L F start q) :
    q ∈ computeWalkable L playable F start := by
  let init := if playable.contains start && !L.isWall start && !F.contains start then [start] else []
  have hinit_eq : init = [start] := by
    have hc1 : playable.contains start = true := List.contains_iff_mem.mpr hstart
    have hc2 : F.contains start = false := by
      cases h : F.contains start
      · rfl
      · exact False.elim (hf0 (List.contains_iff_mem.mp h))
    dsimp only [init]
    rw [hc1, hw0, hc2]
    rfl
  have hinit_sub : SubPos init playable := by
    rw [hinit_eq]
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hstart
  have hinit_nodup : init.Nodup := by
    rw [hinit_eq]
    simp
  have hprops : ∀ ys, SubPos ys playable →
      SubPos ys (walkStep L playable F ys) ∧ SubPos (walkStep L playable F ys) playable :=
    fun ys hys => ⟨(walkStep_props hp ys hys).1, (walkStep_props hp ys hys).2.1⟩
  have hprops_nd : ∀ ys, SubPos ys playable → ys.Nodup →
      SubPos ys (walkStep L playable F ys) ∧ SubPos (walkStep L playable F ys) playable ∧
      (walkStep L playable F ys).Nodup :=
    fun ys hys _ => walkStep_props hp ys hys
  have hfix := iterFixedUp_fixpoint (f := walkStep L playable F) hp hprops_nd playable.length init
    hinit_sub hinit_nodup (by omega)
  have hsub_init : SubPos init (computeWalkable L playable F start) :=
    iterFixedUp_subset_start hprops playable.length init hinit_sub
  have hstart_mem : start ∈ computeWalkable L playable F start := by
    apply hsub_init
    rw [hinit_eq]
    simp
  suffices h : ∀ p₁ p₂, CanWalkAvoiding L F p₁ p₂ →
      p₁ ∈ playable → p₁ ∈ computeWalkable L playable F start →
      p₂ ∈ playable ∧ p₂ ∈ computeWalkable L playable F start by
    exact (h start q hwalk hstart hstart_mem).2
  intro p₁ p₂ hw
  induction hw with
  | refl =>
    intro hp1 hm1
    exact ⟨hp1, hm1⟩
  | @step p r d hwr hfr _ ih =>
    intro hp1 hm1
    have hp_step : step p d ∈ playable := hclosed p hp1 d hwr
    have hm_step : step p d ∈ computeWalkable L playable F start := by
      refine (hfix (step p d)).mp ?_
      simp only [walkStep, List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        List.any_eq_true]
      refine ⟨hp_step, .inr ⟨⟨hwr, ?_⟩, d.opp, Dir.mem_all d.opp, ?_⟩⟩
      · cases hc : F.contains (step p d)
        · rfl
        · exact False.elim (hfr (List.contains_iff_mem.mp hc))
      · rw [step_opp]
        exact List.contains_iff_mem.mpr hm1
    exact ih hp_step hm_step

private theorem walkStep_preserves_canWalk {L : Level} {playable F : List Pos} {start : Pos}
    (acc : List Pos) (hacc : ∀ x ∈ acc, CanWalkAvoiding L F start x) :
    ∀ x ∈ walkStep L playable F acc, CanWalkAvoiding L F start x := by
  intro p hp
  simp only [walkStep, List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    List.any_eq_true] at hp
  rcases hp.2 with hmem | ⟨⟨hwp, hfp⟩, d, _, hd⟩
  · exact hacc p (List.contains_iff_mem.mp hmem)
  · have hstep_acc := hacc (step p d) (List.contains_iff_mem.mp hd)
    have hnotF : p ∉ F := by
      intro hm
      have : F.contains p = true := List.contains_iff_mem.mpr hm
      simp_all
    have hback := canWalkAvoiding_snoc d.opp hstep_acc (by rw [step_opp]; exact hwp)
      (by rw [step_opp]; exact hnotF)
    rw [step_opp] at hback
    exact hback

theorem mem_computeWalkable_canWalkAvoiding {L : Level} {playable F : List Pos} {start q : Pos}
    (hq : q ∈ computeWalkable L playable F start) :
    CanWalkAvoiding L F start q := by
  simp only [computeWalkable] at hq
  let init := if playable.contains start && !L.isWall start && !F.contains start then [start] else []
  have hinit : ∀ x ∈ init, CanWalkAvoiding L F start x := by
    intro x hx
    dsimp only [init] at hx
    split at hx
    · simp only [List.mem_singleton] at hx
      rw [hx]
      exact CanWalkAvoiding.refl _
    · simp at hx
  suffices h : ∀ fuel acc, (∀ x ∈ acc, CanWalkAvoiding L F start x) →
      ∀ x ∈ iterFixedUp (walkStep L playable F) fuel acc, CanWalkAvoiding L F start x from
    h playable.length init hinit q hq
  intro fuel
  induction fuel with
  | zero => intro acc hacc x hx; exact hacc x hx
  | succ n ih =>
    intro acc hacc x hx
    simp only [iterFixedUp] at hx
    split at hx
    · exact hacc x hx
    · exact ih (walkStep L playable F acc) (walkStep_preserves_canWalk acc hacc) x hx

/--
Unified reachability-aware freeze predicate (`IsSuperFrozenSet`).
A set `F` of boxes is *super-frozen* from player position `p₀` if for every box `b ∈ F`
and every push direction `d`, at least one holds:
1. Destination `step b d` is a wall or in `F`,
2. Destination `step b d` is a Simple Dead Square (not in `live`),
3. Pushing side `step b d.opp` is a wall or in `F`, or
4. Player cannot walk from `p₀` to `step b d.opp` avoiding walls and `F`.
-/
def IsSuperFrozenSet (L : Level) (_playable live : List Pos) (p₀ : Pos) (F : List Pos) : Prop :=
  ∀ b ∈ F, ∀ d : Dir,
    (L.isWall (step b d) = true ∨ step b d ∈ F) ∨
    (step b d ∉ live) ∨
    (L.isWall (step b d.opp) = true ∨ step b d.opp ∈ F) ∨
    (¬ CanWalkAvoiding L F p₀ (step b d.opp))

/--
Main Super-Freeze Soundness Theorem:
If `F ⊆ s.boxes` is super-frozen from `s.player` and contains at least one non-goal box,
then `s` is unsolvable (`¬ Solvable L s`).
-/
theorem superFreeze_sound {L : Level} {playable : List Pos} {s₀ : State} {F : List Pos}
    (hv : ValidState L s₀) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s₀.player ∈ playable) (hbox : ∀ b ∈ s₀.boxes, b ∈ playable)
    (hsub : ∀ b ∈ F, b ∈ s₀.boxes)
    (hfrozen : IsSuperFrozenSet L playable (computeLiveSquares L playable) s₀.player F)
    (hnongoal : ∃ b ∈ F, L.isGoal b = false) :
    ¬ Solvable L s₀ := by
  rintro ⟨s_end, hr, hsolved⟩
  suffices h : ∀ {s₁ s₂ : State}, Reach L s₁ s₂ →
      ValidState L s₁ →
      s₁.player ∈ playable →
      (∀ b ∈ s₁.boxes, b ∈ playable) →
      (∀ b ∈ F, b ∈ s₁.boxes) →
      CanWalkAvoiding L F s₀.player s₁.player →
      ¬ IsSolved L s₂ by
    exact h hr hv hpl hbox hsub (CanWalkAvoiding.refl s₀.player) hsolved
  intro s₁ s₂ hr₁₂
  induction hr₁₂ with
  | refl s₁ =>
    intro _ _ _ hF _ hsol
    rcases hnongoal with ⟨b, hbF, hng⟩
    have hg := hsol b (hF b hbF)
    simp_all
  | @step s₁ s₂ s₃ hs hr₂₃ ih =>
    intro hv₁ hpl₁ hbox₁ hF₁ hwalk₁ hsol₃
    have hv₂ := hs.preserves_valid hv₁
    revert hv₁ hpl₁ hbox₁ hF₁ hwalk₁ hv₂
    cases hs with
    | walk d _ hw hnb =>
      intro _ hpl₁ hbox₁ hF₁ hwalk₁ hv₂
      have hpl₂ : step s₁.player d ∈ playable := hclosed s₁.player hpl₁ d hw
      have hnotF : step s₁.player d ∉ F := fun hmem => hnb (hF₁ _ hmem)
      have hwalk₂ := canWalkAvoiding_snoc d hwalk₁ hw hnotF
      exact ih hv₂ hpl₂ hbox₁ hF₁ hwalk₂ hsol₃
    | push d _ hbox_step hw_dest hnb_dest =>
      intro hv₁ _ hbox₁ hF₁ hwalk₁ hv₂
      let b₀ := step s₁.player d
      let dest := step b₀ d
      by_cases hb₀F : b₀ ∈ F
      · have hclause := hfrozen b₀ hb₀F d
        rcases hclause with (hw | hdestF) | hdead | (hpushW | hpushF) | hnowalk
        · dsimp only [b₀] at hw
          simp_all
        · exact hnb_dest (hF₁ dest hdestF)
        · have hdest_play : dest ∈ playable := hclosed b₀ (hbox₁ b₀ hbox_step) d hw_dest
          have hdest_in_s₂ : dest ∈ moveBox s₁.boxes b₀ dest := (mem_moveBox hbox_step).mpr (.inl rfl)
          rcases reach_tracks_box hv₂ hr₂₃ dest hdest_in_s₂ with ⟨g, hg_in, hbr⟩
          have hmem_live := singleBoxReach_goal_mem_liveSquares hp hclosed hdest_play hbr (hsol₃ g hg_in)
          exact hdead hmem_live
        · dsimp only [b₀] at hpushW
          rw [step_opp] at hpushW
          exact absurd hpushW (by simp [hv₁.1])
        · dsimp only [b₀] at hpushF
          rw [step_opp] at hpushF
          exact hv₁.2.1 (hF₁ s₁.player hpushF)
        · dsimp only [b₀] at hnowalk
          rw [step_opp] at hnowalk
          exact hnowalk hwalk₁
      · have hpl₂ : b₀ ∈ playable := hbox₁ b₀ hbox_step
        have hbox₂ : ∀ b ∈ moveBox s₁.boxes b₀ dest, b ∈ playable := by
          intro b hb
          dsimp only [b₀, dest] at hb
          rw [mem_moveBox hbox_step] at hb
          rcases hb with rfl | ⟨hb_old, _⟩
          · exact hclosed b₀ hpl₂ d hw_dest
          · exact hbox₁ b hb_old
        have hF₂ : ∀ b ∈ F, b ∈ moveBox s₁.boxes b₀ dest := by
          intro b hbF
          have hb_old := hF₁ b hbF
          have hne : b ≠ b₀ := fun heq => hb₀F (heq ▸ hbF)
          dsimp only [b₀, dest]
          exact (mem_moveBox hbox_step).mpr (.inr ⟨hb_old, hne⟩)
        have hwalk₂ : CanWalkAvoiding L F s₀.player b₀ :=
          canWalkAvoiding_snoc d hwalk₁ (hv₁.2.2.1 b₀ hbox_step) hb₀F
        exact ih hv₂ hpl₂ hbox₂ hF₂ hwalk₂ hsol₃

/-- Boolean check whether pushing box `b` in direction `d` is blocked relative to `F`, `live`, `walkable`. -/
def dirBlockedBool (L : Level) (live F walkable : List Pos) (b : Pos) (d : Dir) : Bool :=
  let dest := step b d
  let pushPos := step b d.opp
  L.isWall dest || F.contains dest || !live.contains dest ||
  L.isWall pushPos || F.contains pushPos || !walkable.contains pushPos

/-- One greatest-fixed-point pruning iteration removing boxes that can still be validly pushed. -/
def superFreezeStep (L : Level) (playable live : List Pos) (p₀ : Pos) (F : List Pos) : List Pos :=
  let walkable := computeWalkable L playable F p₀
  F.filter (fun b => Dir.all.all (dirBlockedBool L live F walkable b))

/-- Greatest fixed point inside `dedupPos s.boxes` of super-frozen boxes. -/
def computeSuperFrozen (L : Level) (playable live : List Pos) (s : State) : List Pos :=
  let init := dedupPos s.boxes
  iterFixedDown (superFreezeStep L playable live s.player) init.length init

/-- Fast executable Super-Freeze deadlock check given precomputed `live`. -/
def isSuperFreezeDeadlockWithLive (L : Level) (playable live : List Pos) (s : State) : Bool :=
  (computeSuperFrozen L playable live s).any (fun b => !L.isGoal b)

/-- Full executable Super-Freeze deadlock check. -/
def isSuperFreezeDeadlock (L : Level) (playable : List Pos) (s : State) : Bool :=
  let live := computeLiveSquares L playable
  isSuperFreezeDeadlockWithLive L playable live s

private theorem superFreezeStep_props {L : Level} {playable live : List Pos} {p₀ : Pos} :
    ∀ ys, ys.Nodup → SubPos (superFreezeStep L playable live p₀ ys) ys ∧
      (superFreezeStep L playable live p₀ ys).Nodup := by
  intro ys hnd
  refine ⟨?_, nodup_filter hnd⟩
  intro x hx
  simp only [superFreezeStep, List.mem_filter] at hx
  exact hx.1

theorem computeSuperFrozen_isSuperFrozen {L : Level} {playable : List Pos} {s : State}
    (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hv : ValidState L s) (hpl : s.player ∈ playable) :
    IsSuperFrozenSet L playable (computeLiveSquares L playable) s.player
      (computeSuperFrozen L playable (computeLiveSquares L playable) s) := by
  let live := computeLiveSquares L playable
  let init := dedupPos s.boxes
  let F := computeSuperFrozen L playable live s
  have hinit_nd : init.Nodup := nodup_dedupPos s.boxes
  have hfix := iterFixedDown_fixpoint
    (f := superFreezeStep L playable live s.player)
    superFreezeStep_props init.length init hinit_nd (Nat.le_refl _)
  have hF_sub : SubPos F init :=
    iterFixedDown_subset superFreezeStep_props init.length init hinit_nd
  have hp₀_not_F : s.player ∉ F := by
    intro hmem
    have : s.player ∈ init := hF_sub s.player hmem
    rw [mem_dedupPos] at this
    exact hv.2.1 this
  intro b hbF d
  have hmem_step : b ∈ superFreezeStep L playable live s.player F := (hfix b).mpr hbF
  simp only [superFreezeStep, List.mem_filter, List.all_eq_true] at hmem_step
  have hdir := hmem_step.2 d (Dir.mem_all d)
  simp only [dirBlockedBool, Bool.or_eq_true, Bool.not_eq_true'] at hdir
  rcases hdir with (((((hw | hf) | hnlive) | hpw) | hpf) | hnwalk)
  · exact .inl (.inl hw)
  · exact .inl (.inr (List.contains_iff_mem.mp hf))
  · refine .inr (.inl ?_)
    intro hmem
    have : live.contains (step b d) = true := List.contains_iff_mem.mpr hmem
    simp_all
  · exact .inr (.inr (.inl (.inl hpw)))
  · exact .inr (.inr (.inl (.inr (List.contains_iff_mem.mp hpf))))
  · refine .inr (.inr (.inr ?_))
    intro hwalk
    have hmem_w := canWalkAvoiding_mem_computeWalkable hp hclosed hpl hv.1 hp₀_not_F hwalk
    have : (computeWalkable L playable F s.player).contains (step b d.opp) = true :=
      List.contains_iff_mem.mpr hmem_w
    simp_all

theorem superFreezeDeadlockWithLive_sound {L : Level} {playable : List Pos} {s : State}
    (hv : ValidState L s) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s.player ∈ playable) (hbox : ∀ b ∈ s.boxes, b ∈ playable)
    (hdead : isSuperFreezeDeadlockWithLive L playable (computeLiveSquares L playable) s = true) :
    ¬ Solvable L s := by
  let live := computeLiveSquares L playable
  let F := computeSuperFrozen L playable live s
  have hinit_nd : (dedupPos s.boxes).Nodup := nodup_dedupPos s.boxes
  have hF_sub_init : SubPos F (dedupPos s.boxes) :=
    iterFixedDown_subset superFreezeStep_props (dedupPos s.boxes).length (dedupPos s.boxes) hinit_nd
  have hF_sub : ∀ b ∈ F, b ∈ s.boxes := fun b hb => mem_dedupPos.mp (hF_sub_init b hb)
  have hfrozen := computeSuperFrozen_isSuperFrozen hp hclosed hv hpl
  simp only [isSuperFreezeDeadlockWithLive, List.any_eq_true, Bool.not_eq_true'] at hdead
  exact superFreeze_sound hv hp hclosed hpl hbox hF_sub hfrozen hdead

theorem superFreezeDeadlock_sound {L : Level} {playable : List Pos} {s : State}
    (hv : ValidState L s) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s.player ∈ playable) (hbox : ∀ b ∈ s.boxes, b ∈ playable)
    (hdead : isSuperFreezeDeadlock L playable s = true) :
    ¬ Solvable L s :=
  superFreezeDeadlockWithLive_sound hv hp hclosed hpl hbox hdead

/-- Corollary: Classic wall+box freeze set (purely local, no dead squares or player reachability). -/
def IsClassicFrozenSet (L : Level) (F : List Pos) : Prop :=
  ∀ b ∈ F,
    ((L.isWall (step b .left) = true ∨ step b .left ∈ F) ∨
     (L.isWall (step b .right) = true ∨ step b .right ∈ F)) ∧
    ((L.isWall (step b .up) = true ∨ step b .up ∈ F) ∨
     (L.isWall (step b .down) = true ∨ step b .down ∈ F))

theorem classicFrozen_implies_superFrozen {L : Level} {playable live : List Pos} {p₀ : Pos}
    {F : List Pos} (hc : IsClassicFrozenSet L F) :
    IsSuperFrozenSet L playable live p₀ F := by
  intro b hb d
  rcases hc b hb with ⟨hhoriz, hvert⟩
  cases d
  · rcases hvert with hu | hd
    · exact .inl hu
    · rw [Dir.opp]
      exact .inr (.inr (.inl hd))
  · rcases hvert with hu | hd
    · rw [Dir.opp]
      exact .inr (.inr (.inl hu))
    · exact .inl hd
  · rcases hhoriz with hl | hr
    · exact .inl hl
    · rw [Dir.opp]
      exact .inr (.inr (.inl hr))
  · rcases hhoriz with hl | hr
    · rw [Dir.opp]
      exact .inr (.inr (.inl hl))
    · exact .inl hr

theorem classicFreezeDeadlock_sound {L : Level} {playable : List Pos} {s : State} {F : List Pos}
    (hv : ValidState L s) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s.player ∈ playable) (hbox : ∀ b ∈ s.boxes, b ∈ playable)
    (hsub : ∀ b ∈ F, b ∈ s.boxes) (hc : IsClassicFrozenSet L F)
    (hnongoal : ∃ b ∈ F, L.isGoal b = false) :
    ¬ Solvable L s :=
  superFreeze_sound hv hp hclosed hpl hbox hsub (classicFrozen_implies_superFrozen hc) hnongoal

/-- Corollary: A 2×2 block of walls/boxes containing at least one non-goal box is a deadlock. -/
def is2x2Cell (L : Level) (s : State) (p : Pos) : Bool :=
  L.isWall p || s.boxes.contains p

def is2x2Anchor (L : Level) (s : State) (p : Pos) : Bool :=
  let pR := (p.1 + 1, p.2)
  let pD := (p.1, p.2 + 1)
  let pRD := (p.1 + 1, p.2 + 1)
  is2x2Cell L s p && is2x2Cell L s pR && is2x2Cell L s pD && is2x2Cell L s pRD &&
  ([p, pR, pD, pRD].any (fun q => s.boxes.contains q && !L.isGoal q))

theorem block2x2Deadlock_sound {L : Level} {playable : List Pos} {s : State} {p : Pos}
    (hv : ValidState L s) (hp : playable.Nodup) (hclosed : ClosedPlayable L playable)
    (hpl : s.player ∈ playable) (hbox : ∀ b ∈ s.boxes, b ∈ playable)
    (hblock : is2x2Anchor L s p = true) :
    ¬ Solvable L s := by
  let cells := [p, (p.1 + 1, p.2), (p.1, p.2 + 1), (p.1 + 1, p.2 + 1)]
  let F := cells.filter (fun q => s.boxes.contains q)
  simp only [is2x2Anchor, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true'] at hblock
  rcases hblock with ⟨⟨⟨⟨h0, hR⟩, hD⟩, hRD⟩, ⟨q₀, hq₀_cells, hq₀_box, hq₀_ng⟩⟩
  have hcell : ∀ q ∈ cells, L.isWall q = true ∨ q ∈ F := by
    intro q hq
    have hc : is2x2Cell L s q = true := by
      simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> assumption
    simp only [is2x2Cell, Bool.or_eq_true] at hc
    rcases hc with hw | hb
    · exact .inl hw
    · exact .inr (List.mem_filter.mpr ⟨hq, hb⟩)
  have hsub : ∀ b ∈ F, b ∈ s.boxes := by
    intro b hb
    exact List.contains_iff_mem.mp (List.mem_filter.mp hb).2
  have hc : IsClassicFrozenSet L F := by
    intro b hb
    have hb_cells : b ∈ cells := (List.mem_filter.mp hb).1
    simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at hb_cells
    rcases hb_cells with hbp | hbp | hbp | hbp
    · rw [hbp]
      constructor
      · right
        have hstep : step p .right = (p.1 + 1, p.2) := by simp [step]
        rw [hstep]
        exact hcell (p.1 + 1, p.2) (by simp [cells])
      · right
        have hstep : step p .down = (p.1, p.2 + 1) := by simp [step]
        rw [hstep]
        exact hcell (p.1, p.2 + 1) (by simp [cells])
    · rw [hbp]
      constructor
      · left
        have hstep : step (p.1 + 1, p.2) .left = p := by simp [step]
        rw [hstep]
        exact hcell p (by simp [cells])
      · right
        have hstep : step (p.1 + 1, p.2) .down = (p.1 + 1, p.2 + 1) := by simp [step]
        rw [hstep]
        exact hcell (p.1 + 1, p.2 + 1) (by simp [cells])
    · rw [hbp]
      constructor
      · right
        have hstep : step (p.1, p.2 + 1) .right = (p.1 + 1, p.2 + 1) := by simp [step]
        rw [hstep]
        exact hcell (p.1 + 1, p.2 + 1) (by simp [cells])
      · left
        have hstep : step (p.1, p.2 + 1) .up = p := by simp [step]
        rw [hstep]
        exact hcell p (by simp [cells])
    · rw [hbp]
      constructor
      · left
        have hstep : step (p.1 + 1, p.2 + 1) .left = (p.1, p.2 + 1) := by simp [step]
        rw [hstep]
        exact hcell (p.1, p.2 + 1) (by simp [cells])
      · left
        have hstep : step (p.1 + 1, p.2 + 1) .up = (p.1 + 1, p.2) := by simp [step]
        rw [hstep]
        exact hcell (p.1 + 1, p.2) (by simp [cells])
  refine classicFreezeDeadlock_sound hv hp hclosed hpl hbox hsub hc ?_
  exact ⟨q₀, List.mem_filter.mpr ⟨hq₀_cells, hq₀_box⟩, hq₀_ng⟩

end Sokoban
