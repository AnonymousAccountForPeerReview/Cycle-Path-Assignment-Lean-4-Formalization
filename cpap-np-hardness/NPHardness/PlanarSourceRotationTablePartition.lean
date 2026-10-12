module

public import NPHardness.PlanarSourceRotationTableNeighborhood
public import NPHardness.PlanarSourcePackedAddresses

/-! An exact, disjoint partition of the registered grid's indexed occurrences
into the concrete fixed blocks addressed by the compiled program. -/

@[expose] public section
namespace STACS2027.PlanarSource.RotationTable
open Complexity Complexity.SAT Complexity.Planar Complexity.Planar.Grid
open STACS2027.PlanarSource.Packed

def columnBlocks (W k : Nat) (odd : Bool) : List GridBlock :=
  [.start k odd] ++ ((List.range W).reverse.map fun i => .cell k i odd) ++ [.finish k odd]

def blocksByHalf (W m q : Nat) : List GridBlock :=
  ((List.range q).reverse.flatMap fun k => columnBlocks W k false) ++
  ((List.range (m-q)).reverse.flatMap fun k => columnBlocks W k true) ++
  ((List.range (m-q)).reverse.flatMap fun k => (List.range W).reverse.map fun v => .rainbow k v false) ++
  ((List.range (q-1)).reverse.flatMap fun k => (List.range W).reverse.map fun v => .rainbow k v true)

def globalBlocks (W m : Nat) : List GridBlock := blocksByHalf W m ((m+1)/2)

def GridBlock.address (W m q : Nat) (B : GridBlock) (b : Bool) : Nat :=
  match B with
  | .start k odd => Index.columnBase W m q k odd b
  | .cell k idx odd => Index.columnBase W m q k odd b+(if b then 4 else 2)+
      (W-1-idx)*(if b then 48 else 20)
  | .finish k odd => Index.columnBase W m q k odd b+(if b then 4 else 2)+W*(if b then 48 else 20)
  | .rainbow k v odd => Index.rainbowBase W m q k v odd b

theorem half_eq {m q : Nat} (hq : 2*q=m ∨ 2*q=m+1) : (m+1)/2=q := by omega

theorem globalBlocks_eq (W m q : Nat) (hq : 2*q=m ∨ 2*q=m+1) :
    globalBlocks W m=blocksByHalf W m q := by rw [globalBlocks,half_eq hq]

theorem blocksByHalf_mem {W m q : Nat} {B : GridBlock} (hq : 2*q=m ∨ 2*q=m+1) :
    B∈blocksByHalf W m q ↔ B.Valid W m := by
  cases B with
  | start k odd =>
    cases odd <;> simp [blocksByHalf,columnBlocks,GridBlock.Valid,columnIndex] <;> omega
  | finish k odd =>
    cases odd <;> simp [blocksByHalf,columnBlocks,GridBlock.Valid,columnIndex] <;> omega
  | cell k i odd =>
    cases odd <;> simp [blocksByHalf,columnBlocks,GridBlock.Valid,columnIndex] <;> omega
  | rainbow k v odd =>
    cases odd <;> simp [blocksByHalf,columnBlocks,GridBlock.Valid,columnIndex] <;> omega

theorem globalBlocks_mem {W m : Nat} {B : GridBlock} : B∈globalBlocks W m ↔ B.Valid W m := by
  apply blocksByHalf_mem
  omega

theorem GridBlock.blockAt {W m q : Nat} (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (B : GridBlock) (hB : B.Valid W m) :
    Index.BlockAt (gridCNF W m bits) (B.formula W bits) (B.address W m q) := by
  cases B with
  | start k odd =>
    exact Index.grid_start_block W m q k odd bits hq (by cases odd <;> simp_all [GridBlock.Valid,columnIndex] <;> omega)
  | finish k odd =>
    exact Index.grid_end_block W m q k odd bits hq (by cases odd <;> simp_all [GridBlock.Valid,columnIndex] <;> omega)
  | cell k i odd =>
    exact Index.grid_cell_block W m q k i odd bits hq (by cases odd <;> simp_all [GridBlock.Valid,columnIndex] <;> omega) hB.2
  | rainbow k v odd =>
    have h := Index.grid_rainbow_block W m q k v odd bits hq
      (by cases odd <;> simp_all [GridBlock.Valid,columnIndex] <;> omega) hB.2
    cases odd <;> exact h

theorem zipIdx_reverse_blocks {α : Type} (base c n : Nat) (f : Nat → List α)
    (hf : ∀ i, i<n → (f i).length=c) :
    ((List.range n).reverse.flatMap f).zipIdx base =
      (List.range n).reverse.flatMap (fun i => (f i).zipIdx (base+(n-1-i)*c)) := by
  induction n generalizing base with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.reverse_append,List.reverse_singleton,List.singleton_append,
      List.flatMap_cons,List.zipIdx_append,hf n (by omega),ih (base+c) (fun i hi => hf i (by omega))]
    simp only [List.flatMap_cons,Nat.add_sub_cancel,Nat.sub_self,Nat.zero_mul,Nat.add_zero]
    congr 1
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp (List.mem_reverse.mp hi)
    have he : n-i=(n-1-i)+1 := by omega
    rw [he,Nat.add_mul,Nat.one_mul]
    congr 1
    omega

theorem flatten_flatMap {α β : Type} (ls : List α) (f : α → List (List β)) :
    (ls.flatMap f).flatten=ls.flatMap (fun i => (f i).flatten) := by
  rw [List.flatten_eq_flatMap,List.flatMap_assoc]
  simp only [List.flatMap_id]

theorem columnBlocks_partition (W m q k : Nat) (odd : Bool) (bits : Nat → Nat → Bool×Bool) :
    (columnBlocks W k odd).flatMap
      (fun B => (B.formula W bits).flatten.zipIdx (B.address W m q true)) =
      (column W (columnIndex k odd) odd bits).flatten.zipIdx (Index.columnBase W m q k odd true) := by
  rw [column,List.flatten_append,List.flatten_append,List.zipIdx_append,List.zipIdx_append]
  have hs : (startG W (columnIndex k odd)).flatten.length=4 := rfl
  have hc (i : Nat) : (cellCNF W (columnIndex k odd) i odd (bits (columnIndex k odd) (row W odd i))).flatten.length=48 :=
    Index.cell_size true W _ i odd _
  have hm : ((List.range W).reverse.flatMap
      (fun i => cellCNF W (columnIndex k odd) i odd (bits (columnIndex k odd) (row W odd i)))).flatten.length=W*48 := by
    simpa only [Index.size,ite_true,List.length_reverse,List.length_range] using
      Index.size_flatMap_const true (List.range W).reverse _ 48 (fun i _ => hc i)
  rw [hs,List.length_append,hs,hm,flatten_flatMap,
    zipIdx_reverse_blocks _ 48 W _ (fun i _ => hc i)]
  simp only [columnBlocks,List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,GridBlock.formula,GridBlock.address,↓reduceIte,Nat.add_assoc]

theorem rainbowBlocks_partition (W m q k : Nat) (odd : Bool) :
    ((List.range W).reverse.map (fun v => GridBlock.rainbow k v odd)).flatMap
      (fun B => (B.formula W (fun _ _ => (false,false))).flatten.zipIdx (B.address W m q true)) =
      ((List.range W).reverse.flatMap
        (if odd then rbOdd W (columnIndex k odd) else rbEven W (columnIndex k odd))).flatten.zipIdx
        (m*Index.columnSize true W+
          (if odd then (m-q)*(W*4)+(q-2-k)*(W*4) else (m-q-1-k)*(W*4))) := by
  rw [flatten_flatMap,zipIdx_reverse_blocks _ 4 W _ (fun i _ => by cases odd <;> rfl)]
  cases odd <;> simp only [List.flatMap_map,GridBlock.formula,GridBlock.address,Index.rainbowBase,
    Bool.false_eq_true,↓reduceIte]

theorem blocksByHalf_partition (W m q : Nat) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) :
    (blocksByHalf W m q).flatMap (fun B => (B.formula W bits).flatten.zipIdx (B.address W m q true)) =
      (gridCNF W m bits).flatten.zipIdx := by
  let ec := (List.range q).reverse.flatMap (fun k => column W (2*k) false bits)
  let oc := (List.range (m-q)).reverse.flatMap (fun k => column W (2*k+1) true bits)
  let er := (List.range (m-q)).reverse.flatMap (fun k => (List.range W).reverse.flatMap (rbEven W (2*k)))
  let ro := (List.range (q-1)).reverse.flatMap (fun k => (List.range W).reverse.flatMap (rbOdd W (2*k+1)))
  let C := Index.columnSize true W
  have hlen (n : Nat) (f : Nat → CNF) (c : Nat) (h : ∀ i, (f i).flatten.length=c) :
      ((List.range n).reverse.flatMap f).flatten.length=n*c := by
    simpa only [Index.size,ite_true,List.length_reverse,List.length_range] using
      Index.size_flatMap_const true (List.range n).reverse f c (fun i _ => h i)
  have hcl (j : Nat) (o : Bool) : (column W j o bits).flatten.length=C :=
    Index.column_size true W j o bits
  have her (j : Nat) : ((List.range W).reverse.flatMap (rbEven W j)).flatten.length=W*4 :=
    hlen W (rbEven W j) 4 (fun _ => rfl)
  have hro (j : Nat) : ((List.range W).reverse.flatMap (rbOdd W j)).flatten.length=W*4 :=
    hlen W (rbOdd W j) 4 (fun _ => rfl)
  have hec : ec.flatten.length=q*C := hlen q _ C (fun j => hcl (2*j) false)
  have hoc : oc.flatten.length=(m-q)*C := hlen (m-q) _ C (fun j => hcl (2*j+1) true)
  have her' : er.flatten.length=(m-q)*(W*4) := hlen (m-q) _ (W*4) (fun j => her (2*j))
  have hm : q*C+(m-q)*C=m*C := by rw [← Nat.add_mul]; congr 1; omega
  have he : gridCNF W m bits=ec++oc++er++ro := Index.grid_blocks W m q bits hq
  rw [he,List.flatten_append,List.flatten_append,List.flatten_append,
    List.zipIdx_append,List.zipIdx_append,List.zipIdx_append]
  simp only [List.length_append,hec,hoc,her',Nat.zero_add,hm]
  simp only [blocksByHalf,List.flatMap_append,List.flatMap_assoc]
  have heven : (List.range q).reverse.flatMap
      (fun k => (columnBlocks W k false).flatMap
        (fun B => (B.formula W bits).flatten.zipIdx (B.address W m q true))) = ec.flatten.zipIdx := by
    simp only [columnBlocks_partition,ec,flatten_flatMap]
    rw [zipIdx_reverse_blocks 0 C q _ (fun i _ => hcl (2*i) false)]
    simp only [Index.columnBase,Bool.false_eq_true,↓reduceIte,Nat.zero_add,columnIndex,Nat.add_zero]
    rfl
  have hodd : (List.range (m-q)).reverse.flatMap
      (fun k => (columnBlocks W k true).flatMap
        (fun B => (B.formula W bits).flatten.zipIdx (B.address W m q true))) = oc.flatten.zipIdx (q*C) := by
    simp only [columnBlocks_partition,oc,flatten_flatMap]
    rw [zipIdx_reverse_blocks (q*C) C (m-q) _ (fun i _ => hcl (2*i+1) true)]
    rfl
  rw [heven,hodd]
  congr 1
  congr 1
  · simp only [er,flatten_flatMap]
    rw [zipIdx_reverse_blocks (m*C) (W*4) (m-q) _ (fun i _ => by simpa only [flatten_flatMap] using her (2*i))]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro k hk
    have h := rainbowBlocks_partition W m q k false
    simpa only [List.flatMap_map,GridBlock.formula,GridBlock.address,Index.rainbowBase,
      columnIndex,Bool.false_eq_true,↓reduceIte,Nat.add_zero,flatten_flatMap] using h
  · simp only [ro,flatten_flatMap]
    rw [zipIdx_reverse_blocks (m*C+(m-q)*(W*4)) (W*4) (q-1) _ (fun i _ => by simpa only [flatten_flatMap] using hro (2*i+1))]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro k hk
    have h := rainbowBlocks_partition W m q k true
    have heq : q-1-1=q-2 := by omega
    simpa only [List.flatMap_map,GridBlock.formula,GridBlock.address,Index.rainbowBase,
      columnIndex,↓reduceIte,heq,Nat.add_assoc,flatten_flatMap] using h

theorem globalBlocks_partition (W m q : Nat) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) :
    (globalBlocks W m).flatMap (fun B => (B.formula W bits).flatten.zipIdx (B.address W m q true)) =
      (gridCNF W m bits).flatten.zipIdx := by
  rw [globalBlocks_eq W m q hq]
  exact blocksByHalf_partition W m q bits hq

theorem globalBlocks_indices (W m q : Nat) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) :
    (globalBlocks W m).flatMap
      (fun B => ((B.formula W bits).flatten.zipIdx (B.address W m q true)).map Prod.snd) =
      List.range (gridCNF W m bits).flatten.length := by
  have h := congrArg (List.map Prod.snd) (globalBlocks_partition W m q bits hq)
  simpa only [List.map_flatMap,List.zipIdx_map_snd,List.range_eq_range'] using h

theorem globalBlocks_indices_nodup (W m q : Nat) (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) :
    ((globalBlocks W m).flatMap
      (fun B => ((B.formula W bits).flatten.zipIdx (B.address W m q true)).map Prod.snd)).Nodup := by
  rw [globalBlocks_indices W m q bits hq]
  exact List.nodup_range

theorem globalBlocks_occurrence {W m q : Nat} (bits : Nat → Nat → Bool×Bool)
    (hq : 2*q=m ∨ 2*q=m+1) (p : Literal×Nat) :
    p∈(gridCNF W m bits).flatten.zipIdx ↔
      ∃ B : GridBlock, B.Valid W m ∧ p∈(B.formula W bits).flatten.zipIdx (B.address W m q true) := by
  rw [← globalBlocks_partition W m q bits hq,List.mem_flatMap]
  simp only [globalBlocks_mem]

end STACS2027.PlanarSource.RotationTable
