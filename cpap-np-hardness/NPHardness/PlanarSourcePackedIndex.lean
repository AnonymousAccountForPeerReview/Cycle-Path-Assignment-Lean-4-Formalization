module

public import NPHardness.PlanarSourcePackedLayout
public import Complexity.Planar.GridTarget

/-! Exact packed clause/literal addresses for the registered grid order. -/

@[expose] public section
namespace STACS2027.PlanarSource.Packed.Index
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Grid

def size (literal : Bool) (f : CNF) : Nat := if literal then f.flatten.length else f.length

@[simp] theorem size_nil (b : Bool) : size b [] = 0 := by cases b <;> rfl
@[simp] theorem size_append (b : Bool) (f g : CNF) : size b (f++g) = size b f+size b g := by
  cases b <;> simp [size]

theorem size_flatMap_const {α : Type} (b : Bool) (ls : List α) (f : α → CNF) (c : Nat)
    (h : ∀ x ∈ ls, size b (f x)=c) : size b (ls.flatMap f) = ls.length*c := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,size_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    rw [h x (by simp),ih (fun x hx => h x (by simp [hx]))]
    omega

theorem inst_length (o : Nat) (odd : Bool) (c : TCl) : (inst o odd c).length = c.1.length := by
  unfold inst
  split <;> simp

theorem cell_size (b : Bool) (W j idx : Nat) (odd : Bool) (bits : Bool×Bool) :
    size b (cellCNF W j idx odd bits) = if b then 48 else 20 := by
  cases b with
  | false =>
    simp only [size,Bool.false_eq_true,↓reduceIte,cellCNF,List.length_map]
    rcases bits with ⟨bp,bn⟩
    cases bp <;> cases bn <;> rfl
  | true =>
    simp only [size,↓reduceIte,cellCNF,length_flatten',List.map_map]
    have he : (fun x : TCl => (inst (cellOff W j idx) odd x).length) = fun x => x.1.length := by
      funext x
      exact inst_length _ _ x
    change ((cellT bits.1 bits.2).map (fun x => (inst (cellOff W j idx) odd x).length)).sum = 48
    rw [he]
    rcases bits with ⟨bp,bn⟩
    cases bp <;> cases bn <;> rfl

@[simp] theorem start_size (b : Bool) (W j : Nat) : size b (startG W j) = if b then 4 else 2 := by
  cases b <;> rfl
@[simp] theorem end_size (b : Bool) (W j : Nat) : size b (endG W j) = if b then 4 else 2 := by
  cases b <;> rfl
@[simp] theorem evenRainbow_size (b : Bool) (W j v : Nat) : size b (rbEven W j v) = if b then 4 else 2 := by
  cases b <;> rfl
@[simp] theorem oddRainbow_size (b : Bool) (W j v : Nat) : size b (rbOdd W j v) = if b then 4 else 2 := by
  cases b <;> rfl

def columnSize (literal : Bool) (W : Nat) : Nat := if literal then 48*W+8 else 20*W+4

theorem column_size (b : Bool) (W j : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool) :
    size b (column W j odd bits) = columnSize b W := by
  rw [column,size_append,size_append,start_size,end_size,
    size_flatMap_const b _ _ (if b then 48 else 20) (fun _ _ => cell_size _ _ _ _ _ _)]
  simp only [List.length_reverse,List.length_range]
  cases b <;> simp [columnSize,Nat.mul_comm] <;> omega

theorem truncate_reverse_flatMap {α : Type} (m q : Nat) (hq : q ≤ m) (f : Nat → List α) :
    ((List.range m).reverse.flatMap fun k => if k<q then f k else []) =
      (List.range q).reverse.flatMap f := by
  induction m generalizing q with
  | zero =>
    have he : q=0 := by omega
    subst q
    rfl
  | succ m ih =>
    by_cases hqm : q=m+1
    · subst q
      apply congrArg List.flatten
      apply List.map_congr_left
      intro k hk
      have hk' : k<m+1 := List.mem_range.mp (List.mem_reverse.mp hk)
      simp only [ite_eq_left hk']
    · have hq' : q≤m := by omega
      rw [List.range_succ,List.reverse_append,List.reverse_singleton,List.singleton_append,
        List.flatMap_cons,ite_eq_right (by omega : ¬m<q),List.nil_append]
      exact ih q hq'

theorem grid_blocks (W m q : Nat) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) :
    gridCNF W m bits =
      ((List.range q).reverse.flatMap fun k => column W (2*k) false bits) ++
      ((List.range (m-q)).reverse.flatMap fun k => column W (2*k+1) true bits) ++
      ((List.range (m-q)).reverse.flatMap fun k => (List.range W).reverse.flatMap (rbEven W (2*k))) ++
      ((List.range (q-1)).reverse.flatMap fun k => (List.range W).reverse.flatMap (rbOdd W (2*k+1))) := by
  have hqle : q≤m := by omega
  have he : ∀ k, (2*k+1≤m) = (k<q) := fun k => propext (by omega)
  have ho : ∀ k, (2*k+2≤m) = (k<m-q) := fun k => propext (by omega)
  have hr : ∀ k, (2*k+3≤m) = (k<q-1) := fun k => propext (by omega)
  simp only [gridCNF,he,ho,hr]
  rw [truncate_reverse_flatMap m q hqle,
    truncate_reverse_flatMap m (m-q) (by omega),
    truncate_reverse_flatMap m (m-q) (by omega),
    truncate_reverse_flatMap m (q-1) (by omega)]

theorem rainbow_row_size (b : Bool) (W j : Nat) (odd : Bool) :
    size b ((List.range W).reverse.flatMap (if odd then rbOdd W j else rbEven W j)) =
      W*(if b then 4 else 2) := by
  rw [size_flatMap_const b _ _ (if b then 4 else 2)]
  · simp
  · intro v _
    cases odd <;> simp

theorem grid_size (b : Bool) (W m q : Nat) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) :
    size b (gridCNF W m bits) = m*columnSize b W + (m-1)*W*(if b then 4 else 2) := by
  have heven (k : Nat) : size b ((List.range W).reverse.flatMap (rbEven W (2*k))) =
      W*(if b then 4 else 2) := by simpa using rainbow_row_size b W (2*k) false
  have hodd (k : Nat) : size b ((List.range W).reverse.flatMap (rbOdd W (2*k+1))) =
      W*(if b then 4 else 2) := by simpa using rainbow_row_size b W (2*k+1) true
  rw [grid_blocks W m q bits hq]
  simp only [size_append]
  rw [size_flatMap_const b _ _ (columnSize b W) (fun _ _ => column_size _ _ _ _ _),
    size_flatMap_const b _ _ (columnSize b W) (fun _ _ => column_size _ _ _ _ _),
    size_flatMap_const b _ _ (W*(if b then 4 else 2)) (fun k _ => heven k),
    size_flatMap_const b _ _ (W*(if b then 4 else 2)) (fun k _ => hodd k)]
  simp only [List.length_reverse,List.length_range]
  have h1 : q+(m-q)=m := by omega
  have h2 : (m-q)+(q-1)=m-1 := by omega
  calc
    _ = (q+(m-q))*columnSize b W + ((m-q)+(q-1))*(W*(if b then 4 else 2)) := by
      simp only [Nat.add_mul]
      omega
    _ = _ := by rw [h1,h2,Nat.mul_assoc]

end STACS2027.PlanarSource.Packed.Index
