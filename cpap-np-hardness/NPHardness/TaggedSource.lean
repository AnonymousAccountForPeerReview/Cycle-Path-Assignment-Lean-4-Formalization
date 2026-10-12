module

public import NPHardness.SourceReduction

/-! Occurrence splitting with an explicitly supplied universe of copies.
Unused copies are permitted. This permits a compiled rectangular allocation
without runtime searching for the next occurrence of each variable. -/

@[expose] public section
namespace STACS2027
open Complexity.SAT

def taggedWheels (V : Nat) (groups : Nat → List SourceOccurrence) : CNF :=
  (List.range V).flatMap (fun v => sourceWheel (groups v))

def taggedSplit (V : Nat) (groups : Nat → List SourceOccurrence)
    (cs : List (List SourceOccurrence)) : CNF :=
  taggedWheels V groups ++ cs.map sourceCopies

def taggedDecode (groups : Nat → List SourceOccurrence) (a : Assignment) (v : Nat) : Bool :=
  match groups v with
  | [] => false
  | p :: _ => sourceValue a p

theorem exists_values_on_indices (ps : List SourceOccurrence) (hn : (ps.map Prod.snd).Nodup)
    (value : SourceOccurrence → Bool) : ∃ a : Assignment, ∀ p ∈ ps, a p.2 = value p := by
  induction ps with
  | nil => exact ⟨fun _ => false,by simp⟩
  | cons p ps ih =>
    obtain ⟨hp,hps⟩ := List.nodup_cons.mp hn
    obtain ⟨a,ha⟩ := ih hps
    refine ⟨fun i => if i = p.2 then value p else a i,?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simp
    · have hne : q.2 ≠ p.2 := by
        intro he
        exact hp (List.mem_map.mpr ⟨q,hq,he⟩)
      simp [hne,ha q hq]

theorem taggedSplit_bounded (V : Nat) (groups : Nat → List SourceOccurrence)
    (cs : List (List SourceOccurrence))
    (hg : (((List.range V).flatMap groups).map Prod.snd).Nodup)
    (hc : (cs.flatten.map Prod.snd).Nodup)
    (hs : ∀ c ∈ cs, c.length = 2 ∨ c.length = 3) :
    BoundedOccurrence (taggedSplit V groups cs) := by
  have hw (v : Nat) (b : Bool) : occurrences (taggedWheels V groups) v b =
      (((List.range V).flatMap groups).map Prod.snd).count v := by
    have h := sourceWheel_family_occurrences ((List.range V).map groups) v b
    simpa only [taggedWheels,List.flatMap_map,List.flatMap,List.map_map,Function.comp_def] using h
  have hgc (v : Nat) := List.nodup_iff_count.mp hg v
  have hcc (v : Nat) := List.nodup_iff_count.mp hc v
  refine ⟨?_,?_,?_⟩
  · intro c h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp h
      exact Or.inl (sourceWheel_clause_length (groups v) c hv)
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp h
      simpa [sourceCopies] using hs d hd
  · intro v
    rw [taggedSplit,occurrences_append,hw,sourceCopies_occurrences]
    simpa using hgc v
  · intro v
    rw [taggedSplit,occurrences_append,hw,sourceCopies_occurrences]
    simp only [Bool.false_eq_true,↓reduceIte]
    have := hgc v
    have := hcc v
    omega

theorem taggedDecode_value (V : Nat) (groups : Nat → List SourceOccurrence)
    {a : Assignment} (hw : evalCNF a (taggedWheels V groups) = true)
    {v : Nat} (hv : v < V) {p : SourceOccurrence} (hp : p ∈ groups v) :
    sourceValue a p = taggedDecode groups a v := by
  have hh : evalCNF a (sourceWheel (groups v)) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    exact List.all_eq_true.mp hw c (List.mem_flatMap.mpr ⟨v,List.mem_range.mpr hv,hc⟩)
  unfold taggedDecode
  cases hg : groups v with
  | nil => rw [hg] at hp; cases hp
  | cons q qs =>
    rw [hg] at hh hp
    exact sourceWheel_constant hh p hp

theorem taggedSplit_satisfiable (V : Nat) (groups : Nat → List SourceOccurrence)
    (cs : List (List SourceOccurrence))
    (hg : (((List.range V).flatMap groups).map Prod.snd).Nodup)
    (hvar : ∀ v, v < V → ∀ p ∈ groups v, p.1.var = v)
    (hcover : ∀ p ∈ cs.flatten, p.1.var < V ∧ p ∈ groups p.1.var) :
    Satisfiable (taggedSplit V groups cs) ↔ Satisfiable (cs.map (List.map Prod.fst)) := by
  constructor
  · rintro ⟨a,ha⟩
    rw [taggedSplit,evalCNF_append,Bool.and_eq_true] at ha
    refine ⟨taggedDecode groups a,?_⟩
    have he := sourceCopies_eval (taggedDecode groups a) a cs (by
      intro p hp
      obtain ⟨hv,hp⟩ := hcover p hp
      have hv := taggedDecode_value V groups ha.1 hv hp
      unfold sourceValue at hv
      unfold evalLiteral
      rw [← hv]
      cases p.1.positive <;> simp)
    exact he ▸ ha.2
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb⟩ := exists_values_on_indices _ hg (fun p => !(evalLiteral a p.1))
    have hval {v : Nat} (hv : v < V) {p : SourceOccurrence} (hp : p ∈ groups v) :
        b p.2 = !(evalLiteral a p.1) := hb p (List.mem_flatMap.mpr ⟨v,List.mem_range.mpr hv,hp⟩)
    refine ⟨b,?_⟩
    rw [taggedSplit,evalCNF_append,Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro c hc
      obtain ⟨v,hv,hc⟩ := List.mem_flatMap.mp hc
      have hv := List.mem_range.mp hv
      have hh : evalCNF b (sourceWheel (groups v)) = true := by
        apply sourceWheel_of_constant
        intro p hp q hq
        have hpv : sourceValue b p = a v := by
          unfold sourceValue
          rw [hval hv hp]
          cases hs : p.1.positive <;> simp [evalLiteral,hs,hvar v hv p hp]
        have hqv : sourceValue b q = a v := by
          unfold sourceValue
          rw [hval hv hq]
          cases hs : q.1.positive <;> simp [evalLiteral,hs,hvar v hv q hq]
        exact hpv.trans hqv.symm
      exact List.all_eq_true.mp hh c hc
    · have he := sourceCopies_eval a b cs (by
        intro p hp
        obtain ⟨hv,hp⟩ := hcover p hp
        rw [hval hv hp,Bool.not_not])
      exact he.trans ha

end STACS2027
