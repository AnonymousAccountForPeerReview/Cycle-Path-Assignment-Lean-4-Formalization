module

public import NPHardness.PlanarSourceRotationTableCandidates
public import NPHardness.PlanarSourceRotationTablePartition

/-! A duplicate-free local block neighborhood inherits exact occurrence
coverage and uniqueness from the registered grid's global indexed partition. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Grid
open Complexity.StackTableauEmitter STACS2027.PlanarSource.Packed

def blockTags (W m q : Nat) (bits : Nat → Nat → Bool×Bool) (b : GridBlock) : List SourceOccurrence :=
  if b.Valid W m then (b.formula W bits).flatten.zipIdx (b.address W m q true) else []

def neighborhoodTags (W m q : Nat) (bits : Nat → Nat → Bool×Bool) (bs : List GridBlock) :
    List SourceOccurrence := bs.flatMap (blockTags W m q bits)

theorem mem_neighborhoodTags (W m q : Nat) (bits : Nat → Nat → Bool×Bool)
    (bs : List GridBlock) (p : SourceOccurrence) :
    p ∈ neighborhoodTags W m q bits bs ↔
      ∃ b ∈ bs, b.Valid W m ∧ p ∈ (b.formula W bits).flatten.zipIdx (b.address W m q true) := by
  simp only [neighborhoodTags,List.mem_flatMap,blockTags]
  constructor
  · rintro ⟨b,hb,hp⟩
    by_cases hv : b.Valid W m
    · exact ⟨b,hb,hv,by simpa [hv] using hp⟩
    · simp [hv] at hp
  · rintro ⟨b,hb,hv,hp⟩
    exact ⟨b,hb,by simpa [hv] using hp⟩

theorem block_indices_disjoint {W m q : Nat} (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (a b : GridBlock) (ha : a.Valid W m) (hb : b.Valid W m)
    (hne : a ≠ b) :
    ∀ x ∈ ((a.formula W bits).flatten.zipIdx (a.address W m q true)).map Prod.snd,
      ∀ y ∈ ((b.formula W bits).flatten.zipIdx (b.address W m q true)).map Prod.snd, x ≠ y := by
  have hh := (List.pairwise_flatMap.mp (globalBlocks_indices_nodup W m q bits hq)).2
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem (globalBlocks_mem.mpr ha)
  obtain ⟨j,hj,he'⟩ := List.getElem_of_mem (globalBlocks_mem.mpr hb)
  have hij : i ≠ j := by intro h; subst j; exact hne (he.symm.trans he')
  by_cases hlt : i < j
  · have hp := List.pairwise_iff_getElem.mp hh i j hi hj hlt
    rwa [he,he'] at hp
  · have hp := List.pairwise_iff_getElem.mp hh j i hj hi (by omega)
    rw [he,he'] at hp
    intro x hx y hy hxy
    exact hp y hy x hx hxy.symm

theorem neighborhoodTags_indices_nodup {W m q : Nat} (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (bs : List GridBlock) (hbs : bs.Nodup) :
    ((neighborhoodTags W m q bits bs).map Prod.snd).Nodup := by
  rw [neighborhoodTags,List.map_flatMap]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro b hb
    unfold blockTags
    split
    · simp only [List.zipIdx_map_snd]
      exact List.nodup_range'
    · simp
  · apply hbs.imp_of_mem
    intro a b _ _ hne
    unfold blockTags
    by_cases ha : a.Valid W m <;> by_cases hb : b.Valid W m <;> simp only [ha,hb,ite_true,ite_false,List.map_nil]
    · exact block_indices_disjoint bits hq a b ha hb hne
    · intro _ _ _ hy; simp at hy
    · intro _ hx; simp at hx
    · intro _ hx; simp at hx

theorem neighborhoodTags_source {W m q : Nat} (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (bs : List GridBlock) {p : SourceOccurrence}
    (hp : p ∈ neighborhoodTags W m q bits bs) : p ∈ (gridCNF W m bits).flatten.zipIdx := by
  obtain ⟨b,_,hb,hp⟩ := (mem_neighborhoodTags W m q bits bs p).mp hp
  exact (globalBlocks_occurrence bits hq p).mpr ⟨b,hb,hp⟩

/-- Locality of every incident source block yields complete indexed literal
coverage. Equal literals at different indices remain separate occurrences. -/
theorem neighborhoodTags_complete {W m q v : Nat} (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (bs : List GridBlock)
    (hcover : ∀ b, b.Valid W m → ∀ l ∈ (b.formula W bits).flatten, v=l.var → b∈bs)
    {p : SourceOccurrence} (hp : p ∈ (gridCNF W m bits).flatten.zipIdx) (hv : v=p.1.var) :
    p ∈ neighborhoodTags W m q bits bs := by
  obtain ⟨b,hb,hp'⟩ := (globalBlocks_occurrence bits hq p).mp hp
  have hl := List.fst_mem_of_mem_zipIdx hp'
  exact (mem_neighborhoodTags W m q bits bs p).mpr ⟨b,hcover b hb p.1 hl hv,hb,hp'⟩

/-- Active descriptor indices are exactly the live projected occurrences
whose source variable matches the current occurrence. -/
theorem activeIndices_projection {n : Nat} (p : Occurrence n) (xs : List (Occurrence n))
    (w : SAT.Word) (env : Env n) :
    activeIndices (p.eval w env) (xs.map (fun q => q.eval w env)) =
      ((liveProjection xs w env).filter (fun q => q.1.var == p.variable.eval env)).map Prod.snd := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
    by_cases hl : q.live.eval w env = true <;>
      by_cases hv : q.variable.eval env = p.variable.eval env <;>
      simp_all [activeIndices,liveProjection,Occurrence.eval,entryOccurrence]

end STACS2027.PlanarSource.RotationTable
