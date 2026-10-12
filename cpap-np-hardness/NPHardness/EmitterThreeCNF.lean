module

public import NPHardness.EmitterAllocation
public import NPHardness.SourceReduction
public import Complexity.ChainThreeSAT

/-! A fresh-variable 2/3-CNF normalizer for allocated emitter clauses. -/

@[expose] public section
namespace STACS2027
open Complexity Complexity.SAT Complexity.ThreeSAT Complexity.ChainThreeSAT
open Complexity.StackTableauEmitter

def sourceChainChunk (base : Nat) (c : Clause) : CNF :=
  (chainClause base c).map expandSourceUnit

theorem sourceChainChunk_eval (a : Assignment) (base : Nat) (c : Clause) :
    evalCNF a (sourceChainChunk base c) = evalCNF a (chainClause base c) :=
  expandSourceUnits_eval a _

theorem chainEnd_clause_sizes (base : Nat) (c : Clause) :
    ∀ d ∈ chainEnd base c, d.length = 1 ∨ d.length = 3 := by
  induction c generalizing base with
  | nil =>
    intro d hd
    have he : d = [neg base] := by simpa [chainEnd] using hd
    subst d
    exact Or.inl rfl
  | cons l c ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ih _ d hd
    · have he : d = implicationClause base l := by simpa using hd
      subst d
      exact Or.inr rfl

theorem sourceChainChunk_sizes (base : Nat) (c : Clause) :
    ∀ d ∈ sourceChainChunk base c, d.length = 2 ∨ d.length = 3 := by
  intro d hd
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
  have hs : e.length = 1 ∨ e.length = 3 := by
    rcases List.mem_append.mp he with he | he
    · exact chainEnd_clause_sizes base c e he
    · have hh : e = [pos base] := by simpa using he
      subst e
      exact Or.inl rfl
  apply expandSourceUnit_size
  · intro he
    simp [he] at hs
  · omega

theorem expandSourceUnit_mem {l : Literal} {c : Clause} (h : l ∈ expandSourceUnit c) : l ∈ c := by
  cases c with
  | nil => exact h
  | cons a cs => cases cs with
    | nil => simpa [expandSourceUnit] using h
    | cons b bs => exact h

theorem sourceChainChunk_below (base : Nat) (c : Clause) (hc : ClauseBelow base c) :
    CNFBelow (base+c.length+1) (sourceChainChunk base c) := by
  intro d hd l hl
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
  exact chainClause_below base c hc e he l (expandSourceUnit_mem hl)

def allocatedThree (C : Nat) (xs : List (Nat × Clause)) : CNF :=
  xs.flatMap fun x => sourceChainChunk (C+1+x.1*(C+1)) x.2

theorem allocatedThree_sizes (C : Nat) (xs : List (Nat × Clause)) :
    ∀ d ∈ allocatedThree C xs, d.length = 2 ∨ d.length = 3 := by
  intro d hd
  obtain ⟨x,_,hd⟩ := List.mem_flatMap.mp hd
  exact sourceChainChunk_sizes _ _ d hd

theorem allocatedThree_sound (C : Nat) (xs : List (Nat × Clause)) (a : Assignment)
    (h : evalCNF a (allocatedThree C xs) = true) : evalCNF a (xs.map Prod.snd) = true := by
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
  apply chainClause_sound (C+1+x.1*(C+1)) x.2 a
  rw [← sourceChainChunk_eval]
  apply List.all_eq_true.mpr
  intro d hd
  exact List.all_eq_true.mp h d (List.mem_flatMap.mpr ⟨x,hx,hd⟩)

theorem allocatedThree_below (C upper : Nat) (xs : List (Nat × Clause))
    (hs : ∀ x ∈ xs, x.1 < upper)
    (hc : ∀ x ∈ xs, x.2.length ≤ C ∧ ∀ l ∈ x.2, l.var ≤ C) :
    CNFBelow (C+1+upper*(C+1)) (allocatedThree C xs) := by
  intro d hd l hl
  obtain ⟨x,hx,hd⟩ := List.mem_flatMap.mp hd
  have h := sourceChainChunk_below (C+1+x.1*(C+1)) x.2
    (by intro q hq; have := (hc x hx).2 q hq; omega) d hd l hl
  have hm := Nat.mul_le_mul_right (C+1) (show x.1+1 ≤ upper by have := hs x hx; omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  have hn := (hc x hx).1
  omega

theorem allocatedThree_complete (C : Nat) (xs : List (Nat × Clause)) (a : Assignment)
    (hs : xs.Pairwise (fun x y => y.1 < x.1))
    (hc : ∀ x ∈ xs, x.2.length ≤ C ∧ ∀ l ∈ x.2, l.var ≤ C)
    (ha : evalCNF a (xs.map Prod.snd) = true) :
    ∃ b, AgreesBelow (C+1) a b ∧ evalCNF b (allocatedThree C xs) = true := by
  induction xs with
  | nil => exact ⟨a,fun _ _ => rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨hhead,hrest⟩ := Bool.and_eq_true_iff.mp ha
    obtain ⟨horder,ht⟩ := List.pairwise_cons.mp hs
    have hct := fun y hy => hc y (List.mem_cons_of_mem x hy)
    obtain ⟨b,hab,hb⟩ := ih ht hct hrest
    have hx : ClauseBelow (C+1) x.2 := by
      intro l hl
      have h := (hc x List.mem_cons_self).2 l hl
      omega
    have hhead' : evalClause b x.2 = true := (evalClause_agrees hx hab).symm.trans hhead
    have hx' : ClauseBelow (C+1+x.1*(C+1)) x.2 := by
      intro l hl
      have h := hx l hl
      omega
    obtain ⟨b',hbb,hb'⟩ := chainClause_complete _ x.2 b hx' hhead'
    refine ⟨b',fun v hv => (hab v hv).trans (hbb v (by omega)),?_⟩
    change evalCNF b' (sourceChainChunk (C+1+x.1*(C+1)) x.2 ++ allocatedThree C xs) = true
    rw [evalCNF_append,sourceChainChunk_eval,hb',Bool.true_and]
    have hsmall := allocatedThree_below C x.1 xs horder hct
    exact (evalCNF_agrees hsmall hbb).symm.trans hb

theorem allocatedThree_satisfiable {n : Nat} (p : ClauseProgram n) (input : SAT.Word)
    (env : Env n) (C base : Nat) (hf : p.Fits input env C) :
    Satisfiable (allocatedThree C (allocatedEmit p input env C base)) ↔ Satisfiable (p.emit input env) := by
  have he := allocatedEmit_forget p input env C base
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,he ▸ allocatedThree_sound C _ a ha⟩
  · rintro ⟨a,ha⟩
    obtain ⟨b,_,hb⟩ := allocatedThree_complete C _ a
      (allocatedEmit_descending p input env C base hf)
      (allocatedEmit_literals p input env C base hf) (he.symm ▸ ha)
    exact ⟨b,hb⟩

end STACS2027
