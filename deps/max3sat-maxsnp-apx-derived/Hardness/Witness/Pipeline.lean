module

public import Hardness.Witness.Parse
public import Hardness.DecodeList.AlphabetDef
public import Hardness.DecodeList.PoweringDef
public import Hardness.DecodeList.CloudDef
public import Hardness.DecodeList.EndpointsDef
public import ComplexityExt.Witness.Extract

/-!
# The witness decoder as a list program

`decoder` is the word-level decoder of the witness-recovering gap reduction, written against
abstract ingredients so that its polynomial running time (`pt_decoder`) is pure `PT`
reasoning:

* `fb x`: the serialised formula (`formulaBits (toOAI (g₀ x))` in the application);
* `nv x`: its number of variables;
* `I`, `B`, `Pp`: total polynomial-time word functions computing the initial table, one
  amplification round, and the preprocessing (all on unary table codes);
* the constants `q D n N K` of the round decoder and the parameters of `Witness.extract`.

On `x` and an assignment word `y` the decoder

1. computes `w₀ = I (fb x)` and the number of rounds `k` from its header;
2. computes the table codes `w₀, …, w_(k-1)` and `w_k` (`iterList B k w₀`);
3. reads `L_k = finalList (vertices of w_k) y`;
4. folds the round decoder `roundStep` over the round data of `w_(k-1), …, w₀` (`foldRounds`);
5. reads the assignment `initialList (nv x) L₀` and extracts the certificate from it.

The size hypothesis of `pt_decoder` (polynomial length of all iterates `B^[i] w₀`, `i ≤ k`)
is discharged in the application from the size lemmas of the vendored iteration.
-/

@[expose] public section

set_option linter.dupNamespace false

namespace Complexity.WitnessDecode

open Complexity.PT Complexity.PT.Code
open Complexity.DecodeList

/-! ### One round -/

/-- The data of one round: the number of vertices and the tail column of the round input `t`,
the number `V` of vertices of the preprocessed table and the rotation list of the preprocessed
table. -/
abbrev RoundData : Type := Nat × List Nat × Nat × List Nat

/-- The list round decoder: alphabet reduction (the powered table has `V` vertices and
`V * K` darts), powering, and cloud majority. -/
def roundStep (q D n N K : Nat) (d : RoundData) (ℓ : List Nat) : List Nat :=
  cloudList d.1 d.2.1 (powerList D n N d.2.2.1 d.2.2.2 (alphaList q d.2.2.1 (d.2.2.1 * K) ℓ))

theorem pt_roundStep (q D n N K : Nat) :
    PT (fun p : RoundData × List Nat => roundStep q D n N K p.1 p.2) := by
  have hg1 : PT (fun p : RoundData × List Nat => ((p.1.2.2.1, p.1.2.2.1 * K), p.2)) := by
    fun_prop
  have ha : PT (fun p : RoundData × List Nat => alphaList q p.1.2.2.1 (p.1.2.2.1 * K) p.2) :=
    PT.comp (f := fun r : (Nat × Nat) × List Nat => alphaList q r.1.1 r.1.2 r.2)
      (g := fun p : RoundData × List Nat => ((p.1.2.2.1, p.1.2.2.1 * K), p.2))
      (pt_alphaList q) hg1
  have hg2 : PT (fun p : RoundData × List Nat =>
      (p.1.2.2.1, p.1.2.2.2, alphaList q p.1.2.2.1 (p.1.2.2.1 * K) p.2)) :=
    PT.pair (PT.fst (PT.snd (PT.snd (PT.fst PT.id))))
      (PT.pair (PT.snd (PT.snd (PT.snd (PT.fst PT.id)))) ha)
  have hp : PT (fun p : RoundData × List Nat =>
      powerList D n N p.1.2.2.1 p.1.2.2.2 (alphaList q p.1.2.2.1 (p.1.2.2.1 * K) p.2)) :=
    PT.comp (f := fun r : Nat × List Nat × List Nat => powerList D n N r.1 r.2.1 r.2.2)
      (g := fun p : RoundData × List Nat =>
        (p.1.2.2.1, p.1.2.2.2, alphaList q p.1.2.2.1 (p.1.2.2.1 * K) p.2))
      (pt_powerList D n N) hg2
  have hg3 : PT (fun p : RoundData × List Nat =>
      (p.1.1, p.1.2.1,
        powerList D n N p.1.2.2.1 p.1.2.2.2 (alphaList q p.1.2.2.1 (p.1.2.2.1 * K) p.2))) :=
    PT.pair (PT.fst (PT.fst PT.id)) (PT.pair (PT.fst (PT.snd (PT.fst PT.id))) hp)
  exact PT.comp (f := fun r : Nat × List Nat × List Nat => cloudList r.1 r.2.1 r.2.2)
    (g := fun p : RoundData × List Nat => (p.1.1, p.1.2.1,
        powerList D n N p.1.2.2.1 p.1.2.2.2 (alphaList q p.1.2.2.1 (p.1.2.2.1 * K) p.2)))
    pt_cloudList hg3

theorem roundStep_length (q D n N K : Nat) (d : RoundData) (ℓ : List Nat) :
    (roundStep q D n N K d ℓ).length = d.1 := by
  simp [roundStep]

theorem roundStep_le (q D n N K : Nat) (d : RoundData) (ℓ : List Nat) :
    ∀ v ∈ roundStep q D n N K d ℓ, v ≤ 63 := by
  intro v hv
  simp only [roundStep, cloudList, cloudListG, List.mem_map, List.mem_range] at hv
  obtain ⟨_, _, rfl⟩ := hv
  exact OAI.UniqueGamesTheorem.Foundations.PCP.Decode.argMaxUpTo_le _ _

theorem size_roundStep_le (q D n N K : Nat) (d : RoundData) (ℓ : List Nat) :
    size (roundStep q D n N K d ℓ) ≤ 65 * d.1 + 1 := by
  have h := size_map_le (l := roundStep q D n N K d ℓ) (g := fun v => v) (K := 64)
    (fun v hv => by
      have := roundStep_le q D n N K d ℓ v hv
      simp only [size_nat]
      omega)
  rw [List.map_id', roundStep_length] at h
  omega

/-- Fold the round decoder over a list of round data (last round first). -/
def foldRounds (q D n N K : Nat) (ds : List RoundData) (ℓ : List Nat) : List Nat :=
  ds.foldl (fun s d => roundStep q D n N K d s) ℓ

theorem pt_foldRounds (q D n N K : Nat) :
    PT (fun p : List RoundData × List Nat => foldRounds q D n N K p.1 p.2) := by
  refine PT.foldl_of_size_le (f := fun _ s d => roundStep q D n N K d s) (init := fun p => p.2)
    (l := fun p => p.1) ((pt_roundStep q D n N K).comp
      (g := fun p : (List RoundData × List Nat) × List Nat × RoundData => (p.2.2, p.2.1))
      (by fun_prop)) PT.snd' PT.fst' (fun N => 65 * N + 1)
    (((PolynomialBound.constant 65).mul PolynomialBound.identity).add
      (PolynomialBound.constant 1)) ?_
  intro p s d hd
  have h1 := size_roundStep_le q D n N K d s
  have h2 : size d ≤ size p.1 := size_le_of_mem hd
  have h3 : d.1 ≤ size d := by
    simp only [size_prod, size_nat]
    omega
  have h4 : size p.1 ≤ size p := by
    simp only [size_prod]
    omega
  show size (roundStep q D n N K d s) ≤ 65 * size p + 1
  omega

/-! ### Table codes -/

/-- Entry `i` of the header of a table code. -/
def header (w : Word) (i : Nat) : Nat := (unaryWords w).getD i 0

/-- The number of rounds for the initial table code `w`: `log₂ (vertices + darts) + 1`. -/
def roundCount (w : Word) : Nat := Nat.log2 (header w 0 + header w 1) + 1

/-- The round data read off the code `w` of the round input and the code `Pp w` of its
preprocessed table: vertices, tail column, vertices of the preprocessed table, reverse-index
column of the preprocessed table. -/
def dataOf (Pp : Word → Word) (w : Word) : RoundData :=
  (header w 0, column (unaryWords w) 2 4098 (header w 1),
    header (Pp w) 0, column (unaryWords (Pp w)) 3 4098 (header (Pp w) 1))

theorem pt_header : PT (fun p : Word × Nat => header p.1 p.2) := by
  unfold header
  fun_prop

@[fun_prop] protected theorem PT.header {α : Type} [Code α] {w : α → Word} {i : α → Nat}
    (hw : PT w) (hi : PT i) : PT (fun a => header (w a) (i a)) :=
  PT.comp₂ (h := header) pt_header hw hi

theorem pt_roundCount : PT roundCount := by
  unfold roundCount
  fun_prop

theorem pt_dataOf {Pp : Word → Word} (hP : PolyTime Pp) : PT (dataOf Pp) := by
  have hP' : PT Pp := PT.of_polyTime hP
  unfold dataOf
  fun_prop

/-! ### Certificate extraction -/

theorem pt_powerBound (c e : Nat) : PT (fun n : Nat => powerBound c e n) :=
  (PT.mul (PT.const c) (PT.pow_const (PT.succ PT.id) e)).of_eq fun _ => rfl

@[fun_prop] protected theorem PT.powerBound {α : Type} [Code α] (c e : Nat) {f : α → Nat}
    (hf : PT f) : PT (fun a => powerBound c e (f a)) :=
  (pt_powerBound c e).comp hf

theorem pt_extract (states wc wk rc rk : Nat) :
    PT (fun p : Nat × Word => Witness.extract states wc wk rc rk p.1 (SAT.assignmentOf p.2)) := by
  have h : PT (fun p : Nat × Word =>
      ((List.range (powerBound wc wk p.1)).takeWhile
          (fun i => !SAT.assignmentOf p.2
            ((4 * p.1 + powerBound wc wk p.1 + 2 * powerBound rc rk p.1 + i + 4) *
              (states + 4) + 0))).map
        (fun i => SAT.assignmentOf p.2
          ((4 * p.1 + powerBound wc wk p.1 + 2 * powerBound rc rk p.1 + i + 4) *
            (states + 4) + 2))) := by
    fun_prop
  refine h.of_eq fun p => ?_
  rw [Witness.extract_eq]
  simp only [Witness.certVar_eq]

/-! ### The decoder -/

/-- The witness decoder (see the module docstring). -/
def decoder (fb : Word → Word) (nv : Word → Nat) (I B Pp : Word → Word) (q D n N K : Nat)
    (states wc wk rc rk : Nat) (x y : Word) : Word :=
  Witness.extract states wc wk rc rk x.length
    (SAT.assignmentOf
      (initialList (nv x)
        (foldRounds q D n N K
          ((iterList B (roundCount (I (fb x))) (I (fb x))).2.reverse.map (dataOf Pp))
          (finalList (header (iterList B (roundCount (I (fb x))) (I (fb x))).1 0) y))))

/-- **The decoder is polynomial-time**, given polynomial-time ingredients and a polynomial
bound on the lengths of the iterated table codes. -/
theorem pt_decoder {fb : Word → Word} {nv : Word → Nat} {I B Pp : Word → Word}
    (hfb : PT fb) (hnv : PT nv) (hI : PolyTime I) (hB : PolyTime B) (hP : PolyTime Pp)
    (q D n N K : Nat) (states wc wk rc rk : Nat) (c e : Nat)
    (hsize : ∀ x i, i ≤ roundCount (I (fb x)) →
      (B^[i] (I (fb x))).length ≤ powerBound c e (size x)) :
    PT (fun p : Word × Word => decoder fb nv I B Pp q D n N K states wc wk rc rk p.1 p.2) := by
  have hI' : PT I := PT.of_polyTime hI
  have hw0 : PT (fun x => I (fb x)) := hI'.comp hfb
  have hk : PT (fun x => roundCount (I (fb x))) := pt_roundCount.comp hw0
  have hit : PT (fun x => iterList B (roundCount (I (fb x))) (I (fb x))) :=
    pt_iterList hB hw0 hk c e hsize
  have hit' : PT (fun p : Word × Word => iterList B (roundCount (I (fb p.1))) (I (fb p.1))) :=
    hit.comp PT.fst'
  have hdata : PT (fun p : Word × Word =>
      (iterList B (roundCount (I (fb p.1))) (I (fb p.1))).2.reverse.map (dataOf Pp)) :=
    PT.map (f := fun _ w => dataOf Pp w) ((pt_dataOf hP).comp PT.snd') (PT.reverse (PT.snd hit'))
  have hfinal : PT (fun p : Word × Word =>
      finalList (header (iterList B (roundCount (I (fb p.1))) (I (fb p.1))).1 0) p.2) :=
    PT.comp₂ (h := finalList) pt_finalList (PT.header (PT.fst hit') (PT.const 0)) PT.snd'
  have hfold : PT (fun p : Word × Word =>
      foldRounds q D n N K
        ((iterList B (roundCount (I (fb p.1))) (I (fb p.1))).2.reverse.map (dataOf Pp))
        (finalList (header (iterList B (roundCount (I (fb p.1))) (I (fb p.1))).1 0) p.2)) :=
    PT.comp₂ (h := foldRounds q D n N K) (pt_foldRounds q D n N K) hdata hfinal
  have hinit : PT (fun p : Word × Word =>
      initialList (nv p.1)
        (foldRounds q D n N K
          ((iterList B (roundCount (I (fb p.1))) (I (fb p.1))).2.reverse.map (dataOf Pp))
          (finalList (header (iterList B (roundCount (I (fb p.1))) (I (fb p.1))).1 0) p.2))) :=
    PT.comp₂ (h := initialList) pt_initialList (hnv.comp PT.fst') hfold
  exact PT.comp₂ (h := fun m A => Witness.extract states wc wk rc rk m (SAT.assignmentOf A))
    (pt_extract states wc wk rc rk) (PT.length PT.fst') hinit

end Complexity.WitnessDecode
