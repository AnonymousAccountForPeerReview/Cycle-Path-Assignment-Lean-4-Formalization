module

public import NPHardness.PlanarSourcePackedProgram
public import NPHardness.PlanarSourceFormulaSemantics

/-! List-level composition rules connecting exact emitter outputs to the
already verified occurrence-copy and ring formulas. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed
open Complexity Complexity.SAT Complexity.StackTableauEmitter

theorem copiesAt_tagSource (base : Nat) (f : CNF) :
    copiesAt base f = (tagSource base f).map sourceCopies := by
  induction f generalizing base with
  | nil => rfl
  | cons c f ih =>
      have hc : c.zipIdx.map (fun p => (⟨base+p.2,false⟩ : Literal)) =
          sourceCopies (c.zipIdx base) := by
        apply List.ext_getElem
        · simp [sourceCopies]
        · intro i hi hj
          simp [sourceCopies, List.getElem_zipIdx, Nat.add_comm]
      simp only [copiesAt, tagSource, List.map_cons, List.singleton_append, hc, ih]

theorem copiesAt_zero (f : CNF) : copiesAt 0 f = Formula.copyFormula f :=
  copiesAt_tagSource 0 f

theorem copiesAt_append (base : Nat) (f g : CNF) :
    copiesAt base (f ++ g) = copiesAt base f ++ copiesAt (base+f.flatten.length) g := by
  induction f generalizing base with
  | nil => simp [copiesAt]
  | cons c f ih =>
      simp only [List.cons_append, copiesAt, ih, List.flatten_cons, List.length_append,
        List.nil_append, List.cons_append, Nat.add_assoc]

/-- In a reverse counted loop, the packed base is the size of the preceding
blocks.  This proof counts actual source literals, retaining duplicates. -/
theorem copiesAt_reverse_blocks (base size N : Nat) (F : Nat → CNF)
    (hsize : ∀ i, i < N → (F i).flatten.length = size) :
    copiesAt base ((List.range N).reverse.flatMap F) =
      (List.range N).reverse.flatMap
        (fun i => copiesAt (base+(N-1-i)*size) (F i)) := by
  induction N generalizing base with
  | zero => rfl
  | succ N ih =>
      rw [range_reverse_succ_flatMap, copiesAt_append, hsize N (by omega),
        range_reverse_succ_flatMap, ih (base+size) (fun i hi => hsize i (by omega))]
      simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      congr 1
      apply Complexity.Planar.Emit.flatMap_congr_range
      intro i hi
      have he : base+size+(N-1-i)*size = base+(N-i)*size := by
        have hn : N-i = (N-1-i)+1 := by omega
        rw [hn, Nat.add_mul]
        omega
      rw [he]

theorem nodup_eq_singleton {α : Type} {xs : List α} {a : α}
    (hn : xs.Nodup) (hm : ∀ x, x ∈ xs ↔ x = a) : xs = [a] := by
  cases xs with
  | nil => exact False.elim (by have := (hm a).mpr rfl; simp at this)
  | cons x xs =>
      have hx : x = a := (hm x).mp (by simp)
      subst x
      have hz : xs = [] := List.eq_nil_iff_forall_not_mem.mpr (by
        intro x hx
        have ha : x = a := (hm x).mp (by simp [hx])
        subst x
        exact (List.nodup_cons.mp hn).1 hx)
      rw [hz]

/-- Once the local structural proof identifies its single chosen index and
sign, the actual compiled program emits exactly the corresponding ring edge. -/
theorem successorProgram_exact {n : Nat} (p : Occurrence n) (xs : List (Occurrence n))
    (w : SAT.Word) (env : Env n) (next : Nat) (sign : Bool)
    (hn : ((xs.filter (fun q => (successorTest p q xs).eval w env)).map
      (fun q => q.index.eval env)).Nodup)
    (hm : ∀ i, i ∈ (xs.filter (fun q => (successorTest p q xs).eval w env)).map
      (fun q => q.index.eval env) ↔ i = next)
    (hs : ∀ q ∈ xs, (successorTest p q xs).eval w env = true → q.sign.eval w env = sign) :
    (successorProgram p xs).emit w env =
      [[(⟨p.index.eval env,p.sign.eval w env⟩ : Literal),⟨next,!sign⟩]] := by
  have hsel := nodup_eq_singleton hn hm
  have he : (successorProgram p xs).emit w env =
      (xs.filter (fun q => (successorTest p q xs).eval w env)).map
        (fun q => [(⟨p.index.eval env,p.sign.eval w env⟩ : Literal),
          ⟨q.index.eval env,!(q.sign.eval w env)⟩]) := by
    rw [successorProgram_emit]
    have hall : ∀ ys : List (Occurrence n),
        ys.flatMap (fun q => if (successorTest p q xs).eval w env then
          [[(⟨p.index.eval env,p.sign.eval w env⟩ : Literal),
            ⟨q.index.eval env,!(q.sign.eval w env)⟩]] else []) =
        (ys.filter (fun q => (successorTest p q xs).eval w env)).map
          (fun q => [(⟨p.index.eval env,p.sign.eval w env⟩ : Literal),
            ⟨q.index.eval env,!(q.sign.eval w env)⟩]) := by
      intro ys
      induction ys with
      | nil => rfl
      | cons q ys ih =>
          simp only [List.flatMap_cons, List.filter_cons]
          split <;> simp_all
    exact hall xs
  rw [he]
  have hmap : (xs.filter (fun q => (successorTest p q xs).eval w env)).map
      (fun q => [(⟨p.index.eval env,p.sign.eval w env⟩ : Literal),
        ⟨q.index.eval env,!(q.sign.eval w env)⟩]) =
      ((xs.filter (fun q => (successorTest p q xs).eval w env)).map
        (fun q => q.index.eval env)).map
        (fun i => [(⟨p.index.eval env,p.sign.eval w env⟩ : Literal),⟨i,!sign⟩]) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro q hq
    obtain ⟨hqx,hqt⟩ := List.mem_filter.mp hq
    rw [hs q hqx hqt]
    rfl
  rw [hmap, hsel]
  rfl

end STACS2027.PlanarSource.Packed
