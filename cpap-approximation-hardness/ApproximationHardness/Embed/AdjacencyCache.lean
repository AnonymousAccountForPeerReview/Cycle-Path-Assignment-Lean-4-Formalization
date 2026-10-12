module

public import ApproximationHardness.Embed.DFSRAM
import Lean.Elab.Tactic.Omega

/-! # Linear construction of the three-slot adjacency cache -/

@[expose] public section

namespace STACS2027.Embed.DFSRAM

open RAM

def adjacencyPrefix (G : DG) (n v : Nat) : List Nat :=
  (List.range n).filter (fun d => G.rep d == v)

theorem adjacencyPrefix_succ (G : DG) (n v : Nat) :
    adjacencyPrefix G (n+1) v = adjacencyPrefix G n v ++
      (if G.rep n = v then [n] else []) := by
  by_cases h : G.rep n = v <;>
    simp [adjacencyPrefix, List.range_succ, List.filter_append, h]

theorem adjacencyPrefix_full (G : DG) (v : Nat) :
    adjacencyPrefix G (2*G.E) v = G.darts v := rfl

theorem adjacencyPrefix_length (G : DG) {n v : Nat} (hn : n ≤ 2*G.E) :
    (adjacencyPrefix G n v).length ≤ (G.darts v).length := by
  exact ((List.range_sublist.mpr hn).filter (fun d => G.rep d == v)).length_le

theorem getD_snoc (l : List Nat) (x k : Nat) :
    (l ++ [x]).getD k 0 = if k = l.length then x else l.getD k 0 := by
  induction l generalizing k with
  | nil => cases k <;> simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      simpa only [List.cons_append, List.getD_cons_succ, List.length_cons,
        Nat.succ.injEq] using ih k

/-- Store the scanned dart in the next slot of its representative's adjacency list. -/
def adjacencyStep : Stmt := seqs [
  .add 204 160 200, .load 202 204,
  .add 204 162 202, .load 203 204,
  .add 205 203 1, .store 204 205,
  .ifz 203 (seqs [.add 204 163 202, .store 204 200])
    (.seq (.sub 206 203 1) (.ifz 206
      (seqs [.add 204 164 202, .store 204 200])
      (seqs [.add 204 165 202, .store 204 200]))),
  .add 200 200 1, .sub 201 201 1]

def adjacencyLoop : Stmt := .loop 201 adjacencyStep

theorem adjacencyStep_loopFree : LoopFree adjacencyStep := by
  simp [adjacencyStep, LoopFree, seqs]

theorem adjacencyStep_size : size adjacencyStep ≤ 30 := by decide

theorem adjacencyStep_mem (c : Config) (v count : Nat) (hone : c.reg 1 = 1)
    (hv : c.mem (c.reg 160 + c.reg 200) = v)
    (hd : c.mem (c.reg 162 + v) = count) (hc : count < 3) :
    ∀ a, (run adjacencyStep c).mem a =
      if a = c.reg (163+count) + v then c.reg 200 else
        if a = c.reg 162 + v then count+1 else c.mem a := by
  have hs : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases hs with rfl|rfl|rfl <;> intro a <;>
    simp [adjacencyStep, seqs, run, hone, hv, hd]

theorem adjacencyStep_out (c : Config) : (run adjacencyStep c).out = c.out := by
  simp [adjacencyStep, seqs, run]

theorem adjacencyStep_reg (c : Config) (r : Nat)
    (hr : r ≠ 200 ∧ r ≠ 201 ∧ r ≠ 202 ∧ r ≠ 203 ∧ r ≠ 204 ∧ r ≠ 205 ∧ r ≠ 206) :
    (run adjacencyStep c).reg r = c.reg r := by
  rcases hr with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩
  simp [adjacencyStep, seqs, run, h₁,h₂,h₃,h₄,h₅,h₆,h₇]

theorem adjacencyStep_advance (c : Config) (hone : c.reg 1 = 1) :
    (run adjacencyStep c).reg 200 = c.reg 200+1 ∧
      (run adjacencyStep c).reg 201 = c.reg 201-1 := by
  simp [adjacencyStep, seqs, run, hone]

theorem adjacency_cell_eq_iff (L : Layout) {j k i a : Nat}
    (hi : i < L.width) (ha : a < L.width) :
    L.cell j i = L.cell k a ↔ j = k ∧ i = a := by
  constructor
  · intro h
    have hjk : j = k := by
      apply Classical.byContradiction
      intro hn
      dsimp [Layout.cell, Layout.block] at h
      rcases Nat.lt_or_gt_of_ne hn with hjk|hkj
      · have hm := Nat.mul_le_mul_right L.width (show j+1 ≤ k by omega)
        rw [Nat.add_mul] at hm; omega
      · have hm := Nat.mul_le_mul_right L.width (show k+1 ≤ j by omega)
        rw [Nat.add_mul] at hm; omega
    refine ⟨hjk, ?_⟩
    subst k
    dsimp [Layout.cell] at h
    omega
  · rintro ⟨rfl,rfl⟩; rfl

structure AdjacencyState (L : Layout) (G : DG) (start c : Config) (n : Nat) : Prop where
  bases : Bases L G c
  width : 2*G.E ≤ L.width
  bound : n ≤ 2*G.E
  counter : c.reg 200 = n
  remaining : c.reg 201 = 2*G.E-n
  representatives : ∀ d, d < 2*G.E → c.mem (L.cell 0 d) = G.rep d
  partners : ∀ d, d < 2*G.E → c.mem (L.cell 1 d) = STACS2027.Embed.pair d
  degrees : ∀ v, v < 2*G.E → c.mem (L.cell 2 v) = (adjacencyPrefix G n v).length
  adjacent : ∀ k, k < 3 → ∀ v, v < 2*G.E →
    c.mem (L.cell (3+k) v) = (adjacencyPrefix G n v).getD k 0
  preserved : ∀ a, a < L.block 2 ∨ L.block 6 ≤ a → c.mem a = start.mem a

theorem AdjacencyState.smallReg {L : Layout} {G : DG} {start c : Config} {n : Nat}
    (_h : AdjacencyState L G start c n) (r : Nat) (hr : r < 200) :
    (run adjacencyStep c).reg r = c.reg r := by
  apply adjacencyStep_reg
  omega

theorem AdjacencyState.bases_step {L : Layout} {G : DG} {start c : Config} {n : Nat}
    (h : AdjacencyState L G start c n) : Bases L G (run adjacencyStep c) := by
  rcases h.bases with ⟨h₀,h₁,hD,hB,hW,hbase⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [h.smallReg 0 (by decide)]; exact h₀
  · rw [h.smallReg 1 (by decide)]; exact h₁
  · rw [h.smallReg dartCount (by decide)]; exact hD
  · rw [h.smallReg baseRegister (by decide)]; exact hB
  · rw [h.smallReg widthRegister (by decide)]; exact hW
  · intro j hj
    rw [h.smallReg (160+j) (by omega)]
    exact hbase j hj

theorem AdjacencyState.step_cells {L : Layout} {G : DG} {start c : Config} {n : Nat}
    (h : AdjacencyState L G start c n) (hG : G.Ok) (hn : n < 2*G.E)
    (j w : Nat) (hw : w < L.width) :
    (run adjacencyStep c).mem (L.cell j w) =
      if j = 3+(adjacencyPrefix G n (G.rep n)).length ∧ w = G.rep n then n else
      if j = 2 ∧ w = G.rep n then (adjacencyPrefix G n (G.rep n)).length+1
      else c.mem (L.cell j w) := by
  have hv : G.rep n < 2*G.E := hG.rep_lt n hn
  have hcount : (adjacencyPrefix G n (G.rep n)).length < 3 := by
    have hp := adjacencyPrefix_length G (v := G.rep n) (show n+1 ≤ 2*G.E by omega)
    rw [adjacencyPrefix_succ] at hp
    simp only [ite_true,List.length_append,List.length_singleton] at hp
    have := hG.deg (G.rep n)
    omega
  have hbase := h.bases.2.2.2.2.2
  have h160 : c.reg 160 = L.block 0 := hbase 0 (by decide)
  have h162 : c.reg 162 = L.block 2 := hbase 2 (by decide)
  have hslot : c.reg (163+(adjacencyPrefix G n (G.rep n)).length) =
      L.block (3+(adjacencyPrefix G n (G.rep n)).length) := by
    simpa only [← Nat.add_assoc] using hbase
      (3+(adjacencyPrefix G n (G.rep n)).length) (by omega)
  have hrep : c.mem (c.reg 160+c.reg 200) = G.rep n := by
    rw [h160,h.counter]; exact h.representatives n hn
  have hdeg : c.mem (c.reg 162+G.rep n) = (adjacencyPrefix G n (G.rep n)).length := by
    rw [h162]; exact h.degrees _ hv
  have hs := adjacencyStep_mem c (G.rep n) (adjacencyPrefix G n (G.rep n)).length
    h.bases.2.1 hrep hdeg hcount (L.cell j w)
  rw [hslot,h162,h.counter] at hs
  change (run adjacencyStep c).mem (L.cell j w) =
    (if L.cell j w = L.cell (3+(adjacencyPrefix G n (G.rep n)).length) (G.rep n) then n else
     if L.cell j w = L.cell 2 (G.rep n) then (adjacencyPrefix G n (G.rep n)).length+1 else c.mem (L.cell j w)) at hs
  simpa only [adjacency_cell_eq_iff L hw (Nat.lt_of_lt_of_le hv h.width)] using hs

theorem AdjacencyState.step {L : Layout} {G : DG} {start c : Config} {n : Nat}
    (h : AdjacencyState L G start c n) (hG : G.Ok) (hn : n < 2*G.E) :
    AdjacencyState L G start (run adjacencyStep c) (n+1) := by
  have hv := hG.rep_lt n hn
  have ha := adjacencyStep_advance c h.bases.2.1
  refine ⟨h.bases_step,h.width,by omega,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ha.1,h.counter]
  · rw [ha.2,h.remaining]; omega
  · intro d hd
    rw [h.step_cells hG hn 0 d (Nat.lt_of_lt_of_le hd h.width)]
    have hne : 0 ≠ 3+(adjacencyPrefix G n (G.rep n)).length := by omega
    simp only [hne, false_and, ite_false, reduceCtorEq]
    exact h.representatives d hd
  · intro d hd
    rw [h.step_cells hG hn 1 d (Nat.lt_of_lt_of_le hd h.width)]
    have hne : 1 ≠ 3+(adjacencyPrefix G n (G.rep n)).length := by omega
    simp only [hne, false_and, ite_false]
    exact h.partners d hd
  · intro v hvl
    rw [h.step_cells hG hn 2 v (Nat.lt_of_lt_of_le hvl h.width),adjacencyPrefix_succ]
    by_cases he : v = G.rep n
    · subst v
      have hne : 2 ≠ 3+(adjacencyPrefix G n (G.rep n)).length := by omega
      simp [hne]
    · have he' : G.rep n ≠ v := Ne.symm he
      simp [he,he',h.degrees v hvl]
  · intro k hk v hvl
    rw [h.step_cells hG hn (3+k) v (Nat.lt_of_lt_of_le hvl h.width),adjacencyPrefix_succ]
    by_cases he : v = G.rep n
    · subst v
      simp only [and_true, ite_true]
      rw [getD_snoc]
      have hne : 3+k ≠ 2 := by omega
      simp only [Nat.add_left_cancel_iff, hne, ite_false, h.adjacent k hk _ hv]
    · have he' : G.rep n ≠ v := Ne.symm he
      simp [he,he',h.adjacent k hk v hvl]
  · intro a hab
    have hbase := h.bases.2.2.2.2.2
    have hcount : (adjacencyPrefix G n (G.rep n)).length < 3 := by
      have hp := adjacencyPrefix_length G (v := G.rep n) (show n+1 ≤ 2*G.E by omega)
      rw [adjacencyPrefix_succ] at hp
      simp only [ite_true,List.length_append,List.length_singleton] at hp
      have := hG.deg (G.rep n); omega
    have hm := adjacencyStep_mem c (G.rep n) (adjacencyPrefix G n (G.rep n)).length
      h.bases.2.1 (by rw [hbase 0 (by decide),h.counter]; exact h.representatives n hn)
      (by rw [hbase 2 (by decide)]; exact h.degrees _ hv) hcount a
    have hslot : c.reg (163+(adjacencyPrefix G n (G.rep n)).length) =
        L.block (3+(adjacencyPrefix G n (G.rep n)).length) := by
      simpa only [← Nat.add_assoc] using hbase
        (3+(adjacencyPrefix G n (G.rep n)).length) (by omega)
    rw [hslot,hbase 2 (by decide)] at hm
    have hg : G.rep n < L.width := Nat.lt_of_lt_of_le hv h.width
    have hne₁ : a ≠ L.block (3+(adjacencyPrefix G n (G.rep n)).length)+G.rep n := by
      dsimp [Layout.block] at hab ⊢
      have hlo := Nat.mul_le_mul_right L.width (show 2 ≤ 3+(adjacencyPrefix G n (G.rep n)).length by omega)
      have hhi := Nat.mul_le_mul_right L.width (show 3+(adjacencyPrefix G n (G.rep n)).length+1 ≤ 6 by omega)
      rw [Nat.add_mul] at hhi
      omega
    have hne₂ : a ≠ L.block 2+G.rep n := by
      dsimp [Layout.block] at hab ⊢; omega
    rw [ite_eq_right hne₁,ite_eq_right hne₂] at hm
    exact hm.trans (h.preserved a hab)


theorem adjacencyStep_addrOK (S : Nat) (c : Config) (v count : Nat)
    (hone : c.reg 1 = 1) (hv : c.mem (c.reg 160+c.reg 200) = v)
    (hd : c.mem (c.reg 162+v) = count) (hc : count < 3)
    (hr : c.reg 160+c.reg 200 < S) (hdeg : c.reg 162+v < S)
    (hslot : ∀ k, k < 3 → c.reg (163+k)+v < S) : AddrOK S adjacencyStep c := by
  have hs : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases hs with rfl|rfl|rfl <;>
    simp [adjacencyStep, seqs, AddrOK, run, hone, hv, hd, hr, hdeg,
      hslot 0 (by decide),hslot 1 (by decide),hslot 2 (by decide)]

theorem AdjacencyState.addrOK {S : Nat} {L : Layout} {G : DG}
    {start c : Config} {n : Nat} (h : AdjacencyState L G start c n)
    (hG : G.Ok) (hn : n < 2*G.E) (hS : L.limit ≤ S) : AddrOK S adjacencyStep c := by
  have hv := hG.rep_lt n hn
  have hb := h.bases.2.2.2.2.2
  have hcount : (adjacencyPrefix G n (G.rep n)).length < 3 := by
    have hp := adjacencyPrefix_length G (v := G.rep n) (show n+1 ≤ 2*G.E by omega)
    rw [adjacencyPrefix_succ] at hp
    simp only [ite_true,List.length_append,List.length_singleton] at hp
    have := hG.deg (G.rep n); omega
  apply adjacencyStep_addrOK S c (G.rep n) (adjacencyPrefix G n (G.rep n)).length
    h.bases.2.1
  · rw [hb 0 (by decide),h.counter]; exact h.representatives n hn
  · rw [hb 2 (by decide)]; exact h.degrees _ hv
  · exact hcount
  · rw [hb 0 (by decide),h.counter]
    exact Nat.lt_of_lt_of_le (Layout.cell_lt (by decide) (Nat.lt_of_lt_of_le hn h.width)) hS
  · rw [hb 2 (by decide)]
    exact Nat.lt_of_lt_of_le (Layout.cell_lt (by decide) (Nat.lt_of_lt_of_le hv h.width)) hS
  · intro k hk
    have hbase : c.reg (163+k) = L.block (3+k) := by
      simpa only [← Nat.add_assoc] using hb (3+k) (by omega)
    rw [hbase]
    exact Nat.lt_of_lt_of_le (Layout.cell_lt (by omega) (Nat.lt_of_lt_of_le hv h.width)) hS

/-- The actual ascending dart loop fills the entire three-slot cache in linear time. -/
theorem adjacencyLoop_spec {S : Nat} {L : Layout} {G : DG} (hG : G.Ok)
    (hS : L.limit ≤ S) :
    ∀ (r n : Nat) (start c : Config), n+r = 2*G.E →
      AdjacencyState L G start c n →
      ∃ t c', ExecB S adjacencyLoop c t c' ∧ t ≤ 31*r+1 ∧
        AdjacencyState L G start c' (2*G.E) ∧ c'.out = c.out := by
  intro r
  induction r with
  | zero =>
    intro n start c hn hc
    have he : n = 2*G.E := by omega
    subst n
    exact ⟨1,c,.loopDone (by rw [hc.remaining];omega),by simp,hc,rfl⟩
  | succ r ih =>
    intro n start c hn hc
    have hn' : n < 2*G.E := by omega
    have hnz : c.reg 201 ≠ 0 := by rw [hc.remaining]; omega
    have he := execB_run adjacencyStep adjacencyStep_loopFree c (hc.addrOK hG hn' hS)
    have hb := Nat.le_trans (cost_le_size adjacencyStep c) adjacencyStep_size
    obtain ⟨t,c',ht,htime,hfinal,hout⟩ :=
      ih (n+1) start (run adjacencyStep c) (by omega) (hc.step hG hn')
    refine ⟨RAM.cost adjacencyStep c+t+1,c',.loopNext hnz he ht,by omega,hfinal,?_⟩
    exact hout.trans (adjacencyStep_out c)

theorem AdjacencyState.tables {L : Layout} {G : DG} {start c : Config}
    (h : AdjacencyState L G start c (2*G.E)) : Tables L G c := by
  refine ⟨h.representatives,h.partners,?_,?_⟩
  · intro v hv; simpa only [adjacencyPrefix_full] using h.degrees v hv
  · intro k hk v hv; simpa only [adjacencyPrefix_full] using h.adjacent k hk v hv

end STACS2027.Embed.DFSRAM
