module

public import NPHardness.SourceCycle
public import NPHardness.OccurrencePorts
public import NPHardness.ClausePadding

/-! Fresh occurrence labels and exact wheel polarity counts. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def tagSource (next : Nat) : CNF → List (List SourceOccurrence)
  | [] => []
  | c :: f => c.zipIdx next :: tagSource (next+c.length) f

theorem tagSource_forget (next : Nat) (f : CNF) :
    (tagSource next f).map (List.map Prod.fst) = f := by
  induction f generalizing next with
  | nil => rfl
  | cons c f ih => simp [tagSource,ih]

theorem tagSource_flatten (next : Nat) (f : CNF) :
    (tagSource next f).flatten = f.flatten.zipIdx next := by
  induction f generalizing next with
  | nil => rfl
  | cons c f ih => simp [tagSource,ih,List.zipIdx_append]

def sourcePositive (p : SourceOccurrence) : Literal := ⟨p.2,p.1.positive⟩
def sourceNegative (p : SourceOccurrence) : Literal := ⟨p.2,!p.1.positive⟩

theorem sourceChain_flatten_perm (p : SourceOccurrence) (ps : List SourceOccurrence) :
    (sourceChain p ps).flatten.Perm
      (((p :: ps).take ps.length).map sourcePositive ++ ps.map sourceNegative) := by
  induction ps generalizing p with
  | nil => simp [sourceChain]
  | cons q qs ih =>
    change (sourcePositive p :: sourceNegative q :: (sourceChain q qs).flatten).Perm _
    have ht := (ih q).cons (sourceNegative q)
    have hs := List.perm_middle (l₁ := ((q :: qs).take qs.length).map sourcePositive)
      (l₂ := qs.map sourceNegative) (a := sourceNegative q)
    simpa only [List.length_cons,List.take_succ_cons,List.map_cons,List.cons_append] using
      ((ht.trans hs.symm).cons (sourcePositive p))

theorem sourceWheel_flatten_perm (ps : List SourceOccurrence) :
    (sourceWheel ps).flatten.Perm (ps.map sourcePositive ++ ps.map sourceNegative) := by
  cases ps with
  | nil => simp [sourceWheel]
  | cons p ps =>
    have h := sourceChain_flatten_perm p (ps ++ [p])
    have ht : (p :: (ps ++ [p])).take (ps ++ [p]).length = p :: ps := by simp
    rw [ht] at h
    have hp : ((ps ++ [p]).map sourceNegative).Perm ((p :: ps).map sourceNegative) := by
      simp
    exact h.trans (List.Perm.append_left _ hp)

theorem sourceWheel_occurrences (ps : List SourceOccurrence) (v : Nat) (b : Bool) :
    occurrences (sourceWheel ps) v b = (ps.map Prod.snd).count v := by
  rw [occurrences_eq_count,(sourceWheel_flatten_perm ps).count_eq,List.count_append]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.count_cons]
    by_cases hv : p.2 = v
    · cases hb : p.1.positive <;> cases b <;>
        simp [sourcePositive,sourceNegative,hv,hb,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega
    · have h1 : sourcePositive p ≠ ⟨v,b⟩ := by intro h; exact hv (congrArg Literal.var h)
      have h2 : sourceNegative p ≠ ⟨v,b⟩ := by intro h; exact hv (congrArg Literal.var h)
      simp [h1,h2,hv,ih]

def sourceCopies (ps : List SourceOccurrence) : Clause := ps.map fun p => ⟨p.2,false⟩

def sourceGroups (f : CNF) : List (List SourceOccurrence) :=
  (List.range (variableBound f)).map fun v => f.flatten.zipIdx.filter (fun p => p.1.var == v)

def splitSource (f : CNF) : CNF :=
  (tagSource 0 f).map sourceCopies ++ (sourceGroups f).flatMap sourceWheel

theorem sourceGroups_mem {f : CNF} {ps : List SourceOccurrence} (h : ps ∈ sourceGroups f) :
    ∃ v, v < variableBound f ∧ ps = f.flatten.zipIdx.filter (fun p => p.1.var == v) := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  exact ⟨v,List.mem_range.mp hv,rfl⟩

theorem sourceGroups_contains {f : CNF} {p : SourceOccurrence} (hp : p ∈ f.flatten.zipIdx) :
    p ∈ f.flatten.zipIdx.filter (fun q => q.1.var == p.1.var) ∧
      f.flatten.zipIdx.filter (fun q => q.1.var == p.1.var) ∈ sourceGroups f := by
  have hl := List.fst_mem_of_mem_zipIdx hp
  obtain ⟨c,hc,hpc⟩ := List.mem_flatten.mp hl
  refine ⟨by simp [hp],List.mem_map.mpr ⟨p.1.var,List.mem_range.mpr (literal_lt_variableBound hc hpc),rfl⟩⟩

theorem sourceWheel_family_occurrences (pss : List (List SourceOccurrence)) (v : Nat) (b : Bool) :
    occurrences (pss.flatMap sourceWheel) v b = (pss.flatten.map Prod.snd).count v := by
  induction pss with
  | nil => rfl
  | cons ps pss ih =>
    simp only [List.flatMap_cons,occurrences_append,sourceWheel_occurrences,ih,
      List.flatten_cons,List.map_append,List.count_append]

theorem sourceCopies_occurrences (pss : List (List SourceOccurrence)) (v : Nat) (b : Bool) :
    occurrences (pss.map sourceCopies) v b =
      if b then 0 else (pss.flatten.map Prod.snd).count v := by
  rw [occurrences_eq_count]
  have he : (pss.map sourceCopies).flatten = pss.flatten.map (fun p => (⟨p.2,false⟩ : Literal)) := by
    exact List.map_flatten.symm
  rw [he]
  induction pss.flatten with
  | nil => cases b <;> rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.count_cons] at *
    cases b <;> by_cases hp : p.2 = v <;> simp [hp,ih]

end STACS2027
