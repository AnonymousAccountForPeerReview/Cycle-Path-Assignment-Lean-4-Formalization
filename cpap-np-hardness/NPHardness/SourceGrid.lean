module

public import NPHardness.TaggedSource
public import NPHardness.EmitterTransform

/-! Rectangular occurrence copies. Each position reserves both polarities;
the unused polarity still participates in the implication wheel. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def sourceGridFrom (v base : Nat) : Nat → List SourceOccurrence
  | 0 => []
  | n+1 => (⟨v,true⟩,base) :: (⟨v,false⟩,base+1) :: sourceGridFrom v (base+2) n

def sourceGrid (slots v : Nat) : List SourceOccurrence :=
  sourceGridFrom v (v*(2*slots)) slots

theorem sourceGridFrom_indices (v base n : Nat) :
    (sourceGridFrom v base n).map Prod.snd = List.range' base (2*n) := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [sourceGridFrom,List.map_cons,ih,Nat.mul_succ]
    rw [show 2*n+2 = (2*n+1)+1 by omega,List.range'_succ,List.range'_succ]

theorem sourceGrid_indices (slots v : Nat) :
    (sourceGrid slots v).map Prod.snd = List.range' (v*(2*slots)) (2*slots) :=
  sourceGridFrom_indices v _ slots

theorem sourceGridFrom_variable (v base n : Nat) : ∀ p ∈ sourceGridFrom v base n, p.1.var = v := by
  induction n generalizing base with
  | zero => simp [sourceGridFrom]
  | succ n ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    · exact ih _ p hp

theorem sourceGrid_variable (slots v : Nat) : ∀ p ∈ sourceGrid slots v, p.1.var = v :=
  sourceGridFrom_variable v _ slots

theorem sourceGridFrom_mem (v base n j : Nat) (hj : j < n) (sign : Bool) :
    (⟨v,sign⟩,base+2*j+(if sign then 0 else 1)) ∈ sourceGridFrom v base n := by
  induction n generalizing base j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => cases sign <;> simp [sourceGridFrom]
    | succ j =>
      have h := ih (base+2) j (by omega)
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem sourceGrid_mem (slots v j : Nat) (hj : j < slots) (sign : Bool) :
    (⟨v,sign⟩,v*(2*slots)+2*j+(if sign then 0 else 1)) ∈ sourceGrid slots v :=
  sourceGridFrom_mem v _ slots j hj sign

theorem sourceGrid_all_indices (V slots : Nat) :
    (((List.range V).flatMap (sourceGrid slots)).map Prod.snd) = List.range' 0 (V*(2*slots)) := by
  induction V with
  | zero => simp
  | succ V ih =>
    rw [List.range_succ,List.flatMap_append,List.map_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,sourceGrid_indices,ih]
    rw [show (V+1)*(2*slots) = V*(2*slots)+2*slots by rw [Nat.add_mul,Nat.one_mul]]
    simpa only [Nat.zero_add,Nat.one_mul] using
      (List.range'_append (s := 0) (m := V*(2*slots)) (n := 2*slots) (step := 1))

theorem sourceGrid_all_nodup (V slots : Nat) :
    (((List.range V).flatMap (sourceGrid slots)).map Prod.snd).Nodup := by
  rw [sourceGrid_all_indices]
  exact List.nodup_range'

def gridCopyIndex (S slot i : Nat) (l : Literal) : Nat :=
  l.var*(6*S) + (slot*6 + (2*i + if l.positive then 0 else 1))

def gridCopyClause (S slot : Nat) (c : Clause) : List SourceOccurrence :=
  c.zipIdx.map fun p => (p.1,gridCopyIndex S slot p.2 p.1)

def gridCopyFormula (S : Nat) (xs : List (Nat × Clause)) : List (List SourceOccurrence) :=
  xs.map fun x => gridCopyClause S x.1 x.2

theorem gridCopyClause_forget (S slot : Nat) (c : Clause) :
    (gridCopyClause S slot c).map Prod.fst = c := by simp [gridCopyClause,List.map_map,Function.comp_def]

theorem gridCopyFormula_forget (S : Nat) (xs : List (Nat × Clause)) :
    (gridCopyFormula S xs).map (List.map Prod.fst) = xs.map Prod.snd := by
  simp [gridCopyFormula,List.map_map,gridCopyClause_forget,Function.comp_def]

theorem gridCopyClause_length (S slot : Nat) (c : Clause) : (gridCopyClause S slot c).length = c.length := by
  simp [gridCopyClause]

theorem gridCopyClause_cover (S slot : Nat) (c : Clause) (hs : slot < S) (hc : c.length ≤ 3) :
    ∀ p ∈ gridCopyClause S slot c, p ∈ sourceGrid (3*S) p.1.var := by
  intro p hp
  obtain ⟨⟨l,i⟩,hm,rfl⟩ := List.mem_map.mp hp
  have hi := List.snd_lt_of_mem_zipIdx hm
  have h := sourceGrid_mem (3*S) l.var (3*slot+i) (by simp only [Nat.add_zero] at hi; omega) l.positive
  simpa only [gridCopyIndex,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc] using h

theorem gridCopyIndex_local_bound {S slot i : Nat} (hs : slot < S) (hi : i < 3) (l : Literal) :
    slot*6 + (2*i + if l.positive then 0 else 1) < 6*S := by
  cases l.positive <;> simp only [reduceCtorEq,↓reduceIte] <;> omega

theorem gridCopyIndex_injective {S s t i j : Nat} {l r : Literal}
    (hs : s < S) (ht : t < S) (hi : i < 3) (hj : j < 3)
    (he : gridCopyIndex S s i l = gridCopyIndex S t j r) : s = t ∧ i = j := by
  have h := blockVertex_injective (gridCopyIndex_local_bound hs hi l)
    (gridCopyIndex_local_bound ht hj r) he
  have hli : 2*i+(if l.positive then 0 else 1) < 6 := by cases l.positive <;> simp <;> omega
  have hlj : 2*j+(if r.positive then 0 else 1) < 6 := by cases r.positive <;> simp <;> omega
  have h' := blockVertex_injective hli hlj h.2
  refine ⟨h'.1,?_⟩
  have h'' : 2*i+(if l.positive then 0 else 1) = 2*j+(if r.positive then 0 else 1) := h'.2
  have hlbit : (if l.positive then 0 else 1 : Nat) ≤ 1 := by split <;> omega
  have hrbit : (if r.positive then 0 else 1 : Nat) ≤ 1 := by split <;> omega
  omega

theorem gridCopyClause_indices_nodup {S slot : Nat} (hs : slot < S) {c : Clause} (hc : c.length ≤ 3) :
    ((gridCopyClause S slot c).map Prod.snd).Nodup := by
  have hn : (c.zipIdx.map Prod.snd).Nodup := by
    simpa using (List.nodup_range' (s := 0) (n := c.length))
  rw [List.nodup_iff_pairwise_ne,List.pairwise_map] at hn
  simp only [gridCopyClause,List.map_map]
  rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
  apply hn.imp_of_mem
  intro p q hp hq hne he
  have hp' := List.snd_lt_of_mem_zipIdx hp
  have hq' := List.snd_lt_of_mem_zipIdx hq
  exact hne (gridCopyIndex_injective hs hs (by omega) (by omega) he).2

theorem gridCopyFormula_indices_nodup {S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S)
    (hc : ∀ x ∈ xs, x.2.length ≤ 3)
    (hn : xs.Pairwise (fun x y => y.1 < x.1)) :
    ((gridCopyFormula S xs).flatten.map Prod.snd).Nodup := by
  simp only [gridCopyFormula,List.map_flatten,List.map_map]
  change (xs.flatMap fun x => (gridCopyClause S x.1 x.2).map Prod.snd).Nodup
  rw [List.nodup_iff_pairwise_ne,List.pairwise_flatMap]
  constructor
  · intro x hx
    exact gridCopyClause_indices_nodup (hs x hx) (hc x hx)
  · apply hn.imp_of_mem
    intro x y hx hy horder u hu v hv he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hu
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    obtain ⟨s,hss,rfl⟩ := List.mem_map.mp hq
    have hr' := List.snd_lt_of_mem_zipIdx hr
    have hs' := List.snd_lt_of_mem_zipIdx hss
    have he' := gridCopyIndex_injective (hs x hx) (hs y hy)
      (show r.2 < 3 by have := hc x hx; omega)
      (show s.2 < 3 by have := hc y hy; omega) he
    omega

theorem gridCopyFormula_cover {V S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S)
    (hc : ∀ x ∈ xs, x.2.length ≤ 3 ∧ ∀ l ∈ x.2, l.var < V) :
    ∀ p ∈ (gridCopyFormula S xs).flatten,
      p.1.var < V ∧ p ∈ sourceGrid (3*S) p.1.var := by
  intro p hp
  obtain ⟨cs,hcs,hp⟩ := List.mem_flatten.mp hp
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hcs
  refine ⟨?_,gridCopyClause_cover S x.1 x.2 (hs x hx) (hc x hx).1 p hp⟩
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact (hc x hx).2 q.1 (List.fst_mem_of_mem_zipIdx hq)

end STACS2027
