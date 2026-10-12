module

public import NPHardness.PlanarSourcePackedAddresses
public import NPHardness.PlanarSourceRotationTableBlockAt

/-! Every live concrete block descriptor, including descriptors used in
neighbor candidate lists, denotes its actual registered source occurrence.
This includes the angular key, page, original variable, and literal sign. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter Complexity.Planar Comb Grid
open Complexity.Planar.Emit RotationTable

def Layout.bits {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n) : Nat → Nat → Bool × Bool :=
  bitsW w (d.A.eval env) (d.M.eval env) (d.R.eval env) (d.W.eval env)

def Layout.source {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n) : CNF :=
  gridCNF (d.W.eval env) (d.M.eval env) (d.bits w env)

structure DescriptorSound (f : CNF) (p : Entry) : Prop where
  correct : EntryCorrect f p
  source : p.live = true → entryOccurrence p ∈ f.flatten.zipIdx

theorem DescriptorSound.sign {f : CNF} {p : Entry} (h : DescriptorSound f p)
    (hl : p.live = true) : p.sign = Formula.sourceSigns f p.index :=
  sourceOccurrence_sign (h.source hl)

def SoundList {n : Nat} (f : CNF) (w : SAT.Word) (env : Env n) (xs : List (Occurrence n)) : Prop :=
  ∀ p ∈ xs, DescriptorSound f (p.eval w env)

theorem SoundList.append {n : Nat} {f : CNF} {w : SAT.Word} {env : Env n}
    {xs ys : List (Occurrence n)} (hx : SoundList f w env xs) (hy : SoundList f w env ys) :
    SoundList f w env (xs++ys) := by
  intro p hp
  exact (List.mem_append.mp hp).elim (hx p) (hy p)

theorem SoundList.gate {n : Nat} {f : CNF} {w : SAT.Word} {env : Env n}
    {xs : List (Occurrence n)} (hx : SoundList f w env xs) (test : Test n) :
    SoundList f w env (gate test xs) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have h := hx q hq
  constructor
  · intro hl
    change (test.eval w env && q.live.eval w env) = true at hl
    simp only [Bool.and_eq_true] at hl
    exact h.correct hl.2
  · intro hl
    change (test.eval w env && q.live.eval w env) = true at hl
    simp only [Bool.and_eq_true] at hl
    exact h.source hl.2

theorem blockOccurrences_live {n : Nat} (live : Test n) (N K cb lb : NumExpr n)
    (ts : List (Template n)) {p : Occurrence n}
    (hp : p ∈ blockOccurrences live N K cb lb ts) : p.live = live := by
  induction ts generalizing cb lb with
  | nil => simp [blockOccurrences] at hp
  | cons t ts ih =>
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        rfl
      · exact ih (addN cb 1) (addN lb t.literals.length) hp

theorem blockOccurrences_sound {n : Nat} {f : CNF}
    (live : Test n) (N K cb lb : NumExpr n) (ts : List (Template n))
    (w : SAT.Word) (env : Env n)
    (hN : N.eval env = f.length) (hK : K.eval env = nK f)
    (hb : live.eval w env = true → Index.BlockAt f (ts.map (fun t => t.eval w env))
      (fun b => if b then lb.eval env else cb.eval env))
    (htop : live.eval w env = true → ∀ t ∈ ts, t.top = sideOf (t.eval w env)) :
    SoundList f w env (blockOccurrences live N K cb lb ts) := by
  intro p hp
  have he := blockOccurrences_live live N K cb lb ts hp
  have hl : (p.eval w env).live = true → live.eval w env = true := by
    intro hp
    simpa only [Occurrence.eval,he] using hp
  constructor
  · intro hpLive
    exact (blockOccurrences_correct_of_blockAt live N K cb lb ts w env hN hK
      (hb (hl hpLive)) (htop (hl hpLive)) p hp) hpLive
  · intro hpLive
    exact blockOccurrences_source live N K cb lb ts w env (hb (hl hpLive)) hp

theorem Layout.variableCount_source {n : Nat} (d : Layout n) (w : SAT.Word) (env : Env n) :
    d.variableCount.eval env = nK (d.source w env) := by
  by_cases hm : d.M.eval env = 0
  · simp [Layout.variableCount, Layout.source, NumExpr.eval, hm, nK, gridCNF,
      SAT.variableCount]
  · change d.M.eval env * (9*d.W.eval env+3) = SAT.variableCount (gridCNF _ _ _)
    exact (grid_varCount (by omega) (d.bits w env)).symm

theorem Layout.cellTemplates_source {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n) :
    (d.cellTemplates k idx odd).map (fun t => t.eval w env) =
      cellCNF (d.W.eval env) (2*k.eval env+(if odd then 1 else 0)) (idx.eval env) odd
        (d.bits w env (2*k.eval env+(if odd then 1 else 0)) (row (d.W.eval env) odd (idx.eval env))) := by
  simp only [Layout.cellTemplates, cellTemplates_eval, Test.eval, posE_eval, rowE_eval,
    twoE, NumExpr.eval, Layout.bits, bitsW]

theorem bool_cases_eq {α : Type} (F : Bool → α) : (fun b => if b then F true else F false) = F := by
  funext b
  cases b <;> rfl

theorem Layout.cellOccurrences_sound {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.cellOccurrences k idx odd) := by
  apply blockOccurrences_sound
  · exact d.formulaLength_eval env (d.bits w env) hq
  · exact d.variableCount_source w env
  · intro hl
    rw [bool_cases_eq (fun b => (d.cellBase k idx odd b).eval env), d.cellTemplates_source k idx odd w env]
    exact d.cell_block k idx odd w env (d.bits w env) hq hl
  · intro hl
    exact cellTemplates_page _ _ _ _ _ _ w env

theorem Layout.startOccurrences_sound {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.startOccurrences k odd) := by
  apply blockOccurrences_sound
  · exact d.formulaLength_eval env (d.bits w env) hq
  · exact d.variableCount_source w env
  · intro hl
    rw [bool_cases_eq (fun b => (d.columnBase k odd b).eval env), startTemplates_eval]
    exact d.start_block k odd w env (d.bits w env) hq hl
  · intro hl
    exact startTemplates_page _ _ w env

theorem Layout.endOccurrences_sound {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.endOccurrences k odd) := by
  apply blockOccurrences_sound
  · exact d.formulaLength_eval env (d.bits w env) hq
  · exact d.variableCount_source w env
  · intro hl
    rw [bool_cases_eq (fun b => (d.endBase k odd b).eval env), endTemplates_eval]
    exact d.end_block k odd w env (d.bits w env) hq hl
  · intro hl
    exact endTemplates_page _ _ w env

theorem Layout.rainbowOccurrences_sound {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.rainbowOccurrences k v odd) := by
  apply blockOccurrences_sound
  · exact d.formulaLength_eval env (d.bits w env) hq
  · exact d.variableCount_source w env
  · intro hl
    rw [bool_cases_eq (fun b => (d.rainbowBase k v odd b).eval env), rainbowTemplates_eval]
    have h := d.rainbow_block k v odd w env (d.bits w env) hq hl
    cases odd <;> exact h
  · intro hl
    exact rainbowTemplates_page _ _ _ _ w env ((d.rainbowLive_eval k v odd w env).mp hl).2

theorem Layout.chainCandidates_sound {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.chainCandidates k idx odd) :=
  (((d.cellOccurrences_sound k idx odd w env hq).append
    ((d.cellOccurrences_sound k (subN idx 1) odd w env hq).gate _)).append
    ((d.startOccurrences_sound k odd w env hq).gate _)).append
    ((d.endOccurrences_sound k odd w env hq).gate _)

theorem Layout.cellCandidates_sound {n : Nat} (d : Layout n) (k idx : NumExpr n)
    (odd : Bool) (position : Nat) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.cellCandidates k idx odd position) := by
  unfold Layout.cellCandidates
  split
  · exact d.chainCandidates_sound _ _ _ w env hq
  · split
    · exact d.chainCandidates_sound _ _ _ w env hq
    · split
      · apply (d.cellOccurrences_sound _ _ _ w env hq).append
        split
        · exact d.rainbowOccurrences_sound _ _ _ w env hq
        · exact (d.rainbowOccurrences_sound _ _ _ w env hq).gate _
      · split
        · exact (d.cellOccurrences_sound _ _ _ w env hq).append
            (d.rainbowOccurrences_sound _ _ _ w env hq)
        · exact d.cellOccurrences_sound _ _ _ w env hq

theorem Layout.startCandidates_sound {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (position : Nat) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.startCandidates k odd position) := by
  unfold Layout.startCandidates
  split
  · exact d.startOccurrences_sound _ _ w env hq
  · exact d.chainCandidates_sound _ _ _ w env hq

theorem Layout.endCandidates_sound {n : Nat} (d : Layout n) (k : NumExpr n)
    (odd : Bool) (position : Nat) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.endCandidates k odd position) := by
  unfold Layout.endCandidates
  split
  · exact d.chainCandidates_sound _ _ _ w env hq
  · exact d.endOccurrences_sound _ _ w env hq

theorem Layout.rainbowCandidates_sound {n : Nat} (d : Layout n) (k v : NumExpr n)
    (odd : Bool) (endpoint : Nat) (w : SAT.Word) (env : Env n)
    (hq : 2*(d.Q.eval env)=d.M.eval env ∨ 2*(d.Q.eval env)=d.M.eval env+1) :
    SoundList (d.source w env) w env (d.rainbowCandidates k v odd endpoint) := by
  unfold Layout.rainbowCandidates
  split <;> split <;> exact d.cellCandidates_sound _ _ _ _ w env hq

end STACS2027.PlanarSource.Packed
