module

public import NPHardness.BoundedEmitter

/-! The wheel emits the first signed occurrence of every reserved copy.
The source clauses use distinct negative copies afterwards, so their ports
are computable without searching any previously emitted output. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT Complexity.ThreeSAT

theorem placeFormula_append (past : List Literal) (f g : CNF) :
    placeFormula past (f ++ g) = placeFormula past f ++ placeFormula (past ++ f.flatten) g := by
  induction f generalizing past with
  | nil => simp [placeFormula]
  | cons c f ih => simp [placeFormula,ih,List.append_assoc]

theorem placeLiterals_uniform (past ls : List Literal) (r : Nat) (hn : ls.Nodup)
    (hc : ∀ l ∈ ls, past.count l = r) :
    placeLiterals past ls = ls.map (fun l => PlacedLiteral.mk l r) := by
  induction ls generalizing past with
  | nil => rfl
  | cons l ls ih =>
    obtain ⟨hl,ht⟩ := List.nodup_cons.mp hn
    rw [placeLiterals,hc l (by simp),ih (past ++ [l]) ht]
    · rfl
    · intro q hq
      have he : l ≠ q := fun he => hl (he ▸ hq)
      simp [List.count_append,hc q (by simp [hq]),he]

theorem placeFormula_uniform (past : List Literal) (f : CNF) (r : Nat) (hn : f.flatten.Nodup)
    (hc : ∀ l ∈ f.flatten, past.count l = r) :
    placeFormula past f = f.map (List.map (fun l => PlacedLiteral.mk l r)) := by
  induction f generalizing past with
  | nil => rfl
  | cons c f ih =>
    have hn' : (c ++ f.flatten).Nodup := hn
    obtain ⟨hcn,hfn,hdis⟩ := List.nodup_append.mp hn'
    rw [placeFormula,placeLiterals_uniform past c r hcn
      (fun l hl => hc l (List.mem_append_left _ hl)),ih (past ++ c) hfn]
    · rfl
    · intro l hl
      have he : l ∉ c := fun hm => hdis l hm l hl rfl
      rw [List.count_append,List.count_eq_zero.mpr he,Nat.add_zero]
      exact hc l (List.mem_append_right _ hl)

theorem gridWheelFamily_count (V T v : Nat) (b : Bool) :
    (gridWheelFamily V T).flatten.count ⟨v,b⟩ =
      (List.range' 0 (V*(2*T))).count v := by
  rw [(gridWheelFamily_perm V T).flatten.count_eq]
  rw [← occurrences_eq_count]
  have he := sourceWheel_family_occurrences ((List.range V).map (sourceGrid T)) v b
  have he' : occurrences (taggedWheels V (sourceGrid T)) v b =
      (((List.range V).flatMap (sourceGrid T)).map Prod.snd).count v := by
    simpa only [taggedWheels,List.flatMap_map,List.flatMap,List.map_map,Function.comp_def] using he
  rw [sourceGrid_all_indices] at he'
  exact he'

theorem gridWheelFamily_nodup (V T : Nat) : (gridWheelFamily V T).flatten.Nodup := by
  apply List.nodup_iff_count.mpr
  intro l
  rw [gridWheelFamily_count]
  exact List.nodup_iff_count.mp List.nodup_range' _

theorem gridWheelFamily_placement (V T : Nat) :
    placeFormula [] (gridWheelFamily V T) =
      (gridWheelFamily V T).map (List.map (fun l => PlacedLiteral.mk l 0)) :=
  placeFormula_uniform [] _ 0 (gridWheelFamily_nodup V T) (by simp)

theorem sourceCopies_flatten_nodup (cs : List (List SourceOccurrence))
    (hn : (cs.flatten.map Prod.snd).Nodup) : (cs.map sourceCopies).flatten.Nodup := by
  apply List.nodup_iff_count.mpr
  intro l
  rw [← occurrences_eq_count,sourceCopies_occurrences]
  split
  · omega
  · exact List.nodup_iff_count.mp hn _

theorem sourceCopies_placement (V T : Nat) (cs : List (List SourceOccurrence))
    (hn : (cs.flatten.map Prod.snd).Nodup)
    (hb : ∀ p ∈ cs.flatten, p.2 < V*(2*T)) :
    placeFormula (gridWheelFamily V T).flatten (cs.map sourceCopies) =
      (cs.map sourceCopies).map (List.map (fun l => PlacedLiteral.mk l 1)) := by
  apply placeFormula_uniform _ _ 1 (sourceCopies_flatten_nodup cs hn)
  intro l hl
  obtain ⟨c,hc,hl⟩ := List.mem_flatten.mp hl
  obtain ⟨ps,hps,rfl⟩ := List.mem_map.mp hc
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hl
  rw [gridWheelFamily_count]
  have hm : p.2 ∈ List.range' 0 (V*(2*T)) := by simpa using hb p (List.mem_flatten.mpr ⟨ps,hps,hp⟩)
  have hlo := List.count_pos_iff.mpr hm
  have hhi := List.nodup_iff_count.mp (List.nodup_range' (s := 0) (n := V*(2*T))) p.2
  omega

theorem gridCopyFormula_indices_below {V S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S)
    (hc : ∀ x ∈ xs, x.2.length ≤ 3 ∧ ∀ l ∈ x.2, l.var < V) :
    ∀ p ∈ (gridCopyFormula S xs).flatten, p.2 < V*(2*(3*S)) := by
  intro p hp
  obtain ⟨cs,hcs,hp⟩ := List.mem_flatten.mp hp
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hcs
  obtain ⟨⟨l,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  have hil := List.snd_lt_of_mem_zipIdx hi
  have hv := (hc x hx).2 l (List.fst_mem_of_mem_zipIdx hi)
  have hl := gridCopyIndex_local_bound (hs x hx) (show i < 3 by have := (hc x hx).1; omega) l
  have hmul := Nat.mul_le_mul_right (6*S) (show l.var+1 ≤ V by omega)
  rw [Nat.add_mul,Nat.one_mul] at hmul
  dsimp only [gridCopyIndex]
  have hm : 2*(3*S) = 6*S := by omega
  rw [hm]
  omega

def gridBoundedFormula (V S : Nat) (xs : List (Nat × Clause)) : CNF :=
  gridWheelFamily V (3*S) ++ (gridCopyFormula S xs).map sourceCopies

theorem gridBoundedFormula_placement {V S : Nat} {xs : List (Nat × Clause)}
    (hs : ∀ x ∈ xs, x.1 < S)
    (hc : ∀ x ∈ xs, x.2.length ≤ 3 ∧ ∀ l ∈ x.2, l.var < V)
    (hn : xs.Pairwise (fun x y => y.1 < x.1)) :
    placeFormula [] (gridBoundedFormula V S xs) =
      (gridWheelFamily V (3*S)).map (List.map (fun l => PlacedLiteral.mk l 0)) ++
        ((gridCopyFormula S xs).map sourceCopies).map (List.map (fun l => PlacedLiteral.mk l 1)) := by
  rw [gridBoundedFormula,placeFormula_append,gridWheelFamily_placement,List.nil_append,
    sourceCopies_placement V (3*S) _ (gridCopyFormula_indices_nodup hs (fun x hx => (hc x hx).1) hn)
      (gridCopyFormula_indices_below hs hc)]

end STACS2027
