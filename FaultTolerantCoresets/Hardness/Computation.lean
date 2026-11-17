import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An explicit bit-cost model for the reduction

Programs are finite syntax over first-order values: binary natural numbers,
booleans, pairs, and lists. Arithmetic is charged by operand bit length;
structural operations pay for the values they traverse or copy. General
bounded iteration is included and is *not* automatically polynomial-time.
Polynomial time requires a bound on both evaluated cost and output size.

This is a concrete functional cost model, not a predicate on arbitrary Lean
functions with a caller-supplied running time. No Turing-machine compiler or
machine-model equivalence is assumed or proved here.
-/

namespace FTC.Hardness.Computation

inductive Ty where
  | nat
  | bool
  | pair : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq, Repr

@[reducible] def Ty.Value : Ty → Type
  | .nat => ℕ
  | .bool => Bool
  | .pair a b => a.Value × b.Value
  | .list a => List a.Value

def Ty.size : (t : Ty) → t.Value → ℕ
  | .nat, n => n.size + 1
  | .bool, _ => 1
  | .pair a b, x => a.size x.1 + b.size x.2 + 1
  | .list a, xs => (xs.map a.size).sum + xs.length + 1

@[simp] theorem Ty.size_nat (n : ℕ) : Ty.nat.size n = n.size + 1 := rfl
@[simp] theorem Ty.size_bool (b : Bool) : Ty.bool.size b = 1 := rfl
@[simp] theorem Ty.size_pair {a b : Ty} (x : (Ty.pair a b).Value) :
    (Ty.pair a b).size x = a.size x.1 + b.size x.2 + 1 := rfl
@[simp] theorem Ty.size_list {a : Ty} (xs : List a.Value) :
    (Ty.list a).size xs = (xs.map a.size).sum + xs.length + 1 := rfl

theorem Ty.size_pos (t : Ty) (x : t.Value) : 0 < t.size x := by
  cases t <;> simp only [Ty.size] <;> omega

theorem Ty.size_mem_le {t : Ty} {xs : List t.Value} {x : t.Value} (hx : x ∈ xs) :
    t.size x ≤ (Ty.list t).size xs := by
  have h := List.single_le_sum (l := xs.map t.size) (fun n _ => Nat.zero_le n) _
    (List.mem_map_of_mem hx)
  simp only [Ty.size]
  omega

theorem size_add_le (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  rw [Nat.size_le]
  have ha : a < 2 ^ (a.size + b.size) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hb : b < 2 ^ (a.size + b.size) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  rw [pow_succ]
  omega

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b) (Nat.zero_le _) (Nat.zero_le _)

theorem size_sub_le (a b : ℕ) : (a - b).size ≤ a.size := by
  rw [Nat.size_le]
  exact (Nat.sub_le a b).trans_lt (Nat.lt_size_self a)

def maximum : List ℕ → ℕ
  | [] => 0
  | a :: xs => max a (maximum xs)

theorem le_maximum_of_mem {x : ℕ} {xs : List ℕ} (hx : x ∈ xs) : x ≤ maximum xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact (ih hx).trans (Nat.le_max_right _ _)

theorem maximum_size_le (xs : List ℕ) :
    (maximum xs).size ≤ (xs.map fun n => n.size + 1).sum := by
  induction xs with
  | nil => simp [maximum]
  | cons a xs ih =>
    simp only [maximum, List.map_cons, List.sum_cons]
    by_cases h : a ≤ maximum xs
    · rw [max_eq_right h]
      omega
    · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))]
      omega

/-- Value iteration, with one charged loop step per iteration. -/
def iterateValue {A : Type} (f : A → A) : ℕ → A → A
  | 0, x => x
  | n + 1, x => iterateValue f n (f x)

def iterateCost {A : Type} (f : A → A) (charge : A → ℕ) : ℕ → A → ℕ
  | 0, _ => 1
  | n + 1, x => charge x + iterateCost f charge n (f x) + 1

/-- A closed programming language. In particular, no constructor accepts an
arbitrary function together with an invented cost. -/
inductive Code : Ty → Ty → Type where
  | id {a} : Code a a
  | const {a b} (v : b.Value) : Code a b
  | comp {a b c} : Code a b → Code b c → Code a c
  | pair {a b c} : Code a b → Code a c → Code a (.pair b c)
  | fst {a b} : Code (.pair a b) a
  | snd {a b} : Code (.pair a b) b
  | branch {a b} : Code a .bool → Code a b → Code a b → Code a b
  | add : Code (.pair .nat .nat) .nat
  | mul : Code (.pair .nat .nat) .nat
  | sub : Code (.pair .nat .nat) .nat
  | div : Code (.pair .nat .nat) .nat
  | mod : Code (.pair .nat .nat) .nat
  | le : Code (.pair .nat .nat) .bool
  | eq : Code (.pair .nat .nat) .bool
  | cons {a} : Code (.pair a (.list a)) (.list a)
  | append {a} : Code (.pair (.list a) (.list a)) (.list a)
  | head {a} : Code (.pair a (.list a)) a
  | tail {a} : Code (.list a) (.list a)
  | length {a} : Code (.list a) .nat
  | map {a b} : Code a b → Code (.list a) (.list b)
  | mapWith {s a b} : Code (.pair s a) b → Code (.pair s (.list a)) (.list b)
  | flatten {a} : Code (.list (.list a)) (.list a)
  | maximum : Code (.list .nat) .nat
  | size {a} : Code a .nat
  | range : Code .nat (.list .nat)
  | iterate {a} : Code a a → Code (.pair .nat a) a

def Code.eval : {a b : Ty} → Code a b → a.Value → b.Value
  | _, _, .id, x => x
  | _, _, .const v, _ => v
  | _, _, .comp f g, x => g.eval (f.eval x)
  | _, _, .pair f g, x => (f.eval x, g.eval x)
  | _, _, .fst, x => x.1
  | _, _, .snd, x => x.2
  | _, _, .branch c f g, x => if c.eval x then f.eval x else g.eval x
  | _, _, .add, x => x.1 + x.2
  | _, _, .mul, x => x.1 * x.2
  | _, _, .sub, x => x.1 - x.2
  | _, _, .div, x => x.1 / x.2
  | _, _, .mod, x => x.1 % x.2
  | _, _, .le, x => decide (x.1 ≤ x.2)
  | _, _, .eq, x => decide (x.1 = x.2)
  | _, _, .cons, x => x.1 :: x.2
  | _, _, .append, x => x.1 ++ x.2
  | _, _, .head, x => x.2.headD x.1
  | _, _, .tail, x => x.tail
  | _, _, .length, x => x.length
  | _, _, .map f, x => x.map f.eval
  | _, _, .mapWith f, x => x.2.map (fun y => f.eval (x.1, y))
  | _, _, .flatten, x => x.flatten
  | _, _, .maximum, x => Computation.maximum x
  | a, _, .size, x => a.size x
  | _, _, .range, x => List.range x
  | _, _, .iterate f, x => iterateValue f.eval x.1 x.2

def Code.cost : {a b : Ty} → Code a b → a.Value → ℕ
  | a, _, .id, x => a.size x + 1
  | _, b, .const v, _ => b.size v + 1
  | _, _, .comp f g, x => f.cost x + g.cost (f.eval x) + 1
  | _, _, .pair f g, x => f.cost x + g.cost x + 1
  | _, _, .branch c f g, x => c.cost x + (if c.eval x then f.cost x else g.cost x) + 1
  | _, _, .map f, xs => (xs.map f.cost).sum + (Ty.list _).size xs + 1
  | _, _, .mapWith f, x => (x.2.map (fun y => f.cost (x.1, y))).sum +
      (Ty.pair _ (.list _)).size x + 1
  | _, _, .iterate f, x => iterateCost f.eval f.cost x.1 x.2 + (Ty.pair .nat _).size x
  | _, _, .range, n => (n + 1) ^ 2 * (n.size + 1)
  | a, _, _, x => (a.size x + 1) ^ 2

def bound (C d n : ℕ) : ℕ := C * (n + 1) ^ d

theorem bound_mono {C C' d d' n n' : ℕ}
    (hC : C ≤ C') (hd : d ≤ d') (hn : n ≤ n') : bound C d n ≤ bound C' d' n' := by
  unfold bound
  exact Nat.mul_le_mul hC ((Nat.pow_le_pow_left (by omega) d).trans
    (Nat.pow_le_pow_right (by omega) hd))

theorem bound_add {C d E e n u v : ℕ}
    (hu : u ≤ bound C d n) (hv : v ≤ bound E e n) :
    u + v ≤ bound (C + E) (d + e) n := by
  have hu' := hu.trans (bound_mono le_rfl (Nat.le_add_right d e) le_rfl)
  have hv' := hv.trans (bound_mono le_rfl (Nat.le_add_left e d) le_rfl)
  simpa only [bound, add_mul] using Nat.add_le_add hu' hv'

theorem bound_comp {C d E e n m : ℕ} (hm : m ≤ bound C d n) :
    bound E e m ≤ bound (E * (C + 1) ^ e) (d * e) n := by
  unfold bound at *
  have hone : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d (n + 1) (by omega)
  calc
    E * (m + 1) ^ e ≤ E * ((C + 1) * (n + 1) ^ d) ^ e := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      nlinarith
    _ = E * (C + 1) ^ e * (n + 1) ^ (d * e) := by
      rw [mul_pow, ← pow_mul]
      ring

/-- Both actual charged computation and the materialized result have a
polynomial bound in the binary/structural input size. -/
def Code.IsPoly {a b : Ty} (p : Code a b) : Prop :=
  ∃ C d : ℕ, ∀ x, p.cost x + b.size (p.eval x) ≤ bound C d (a.size x)

theorem Code.poly_of_size_le {a b : Ty} (p : Code a b)
    (hcost : ∀ x, p.cost x ≤ (a.size x + 1) ^ 2)
    (hsize : ∀ x, b.size (p.eval x) ≤ a.size x + 1) : p.IsPoly := by
  refine ⟨2, 2, ?_⟩
  intro x
  have hc := hcost x
  have hs := hsize x
  unfold bound
  nlinarith

theorem Code.poly_id {a : Ty} : (Code.id (a := a)).IsPoly := by
  refine ⟨2, 1, ?_⟩
  intro x
  simp only [Code.cost, Code.eval, bound, pow_one]
  omega

theorem Code.poly_const {a b : Ty} (v : b.Value) : (Code.const (a := a) v).IsPoly := by
  refine ⟨2 * b.size v + 1, 0, ?_⟩
  intro x
  simp only [Code.cost, Code.eval, bound, pow_zero, Nat.mul_one]
  omega

theorem Code.IsPoly.comp {a b c : Ty} {f : Code a b} {g : Code b c}
    (hf : f.IsPoly) (hg : g.IsPoly) : (Code.comp f g).IsPoly := by
  obtain ⟨C, d, hf⟩ := hf
  obtain ⟨E, e, hg⟩ := hg
  refine ⟨C + E * (C + 1) ^ e + 1, d + d * e + 0, ?_⟩
  intro x
  have hfx := hf x
  have hsize : b.size (f.eval x) ≤ bound C d (a.size x) := by omega
  have hsecond := (hg (f.eval x)).trans (bound_comp hsize)
  have hfirst : f.cost x ≤ bound C d (a.size x) := by omega
  have hsum := bound_add hfirst hsecond
  have hone : 1 ≤ bound 1 0 (a.size x) := by simp [bound]
  have htotal := bound_add hsum hone
  simpa only [Code.cost, Code.eval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

theorem Code.IsPoly.pair {a b c : Ty} {f : Code a b} {g : Code a c}
    (hf : f.IsPoly) (hg : g.IsPoly) : (Code.pair f g).IsPoly := by
  obtain ⟨C, d, hf⟩ := hf
  obtain ⟨E, e, hg⟩ := hg
  refine ⟨C + E + 2, d + e + 0, ?_⟩
  intro x
  have hsum := bound_add (hf x) (hg x)
  have htwo : 2 ≤ bound 2 0 (a.size x) := by simp [bound]
  have htotal := bound_add hsum htwo
  simp only [Code.cost, Code.eval, Ty.size]
  omega

theorem Code.poly_fst {a b : Ty} : (Code.fst (a := a) (b := b)).IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  simp only [Code.eval, Ty.size]
  omega

theorem Code.poly_snd {a b : Ty} : (Code.snd (a := a) (b := b)).IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  simp only [Code.eval, Ty.size]
  omega

theorem Code.poly_add : Code.add.IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  have := size_add_le x.1 x.2
  simp only [Code.eval, Ty.size]
  omega

theorem Code.poly_mul : Code.mul.IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  have := size_mul_le x.1 x.2
  simp only [Code.eval, Ty.size]
  omega

theorem Code.poly_sub : Code.sub.IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  have := size_sub_le x.1 x.2
  simp only [Code.eval, Ty.size]
  omega

theorem Code.poly_maximum : Code.maximum.IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  change (Computation.maximum x).size + 1 ≤
    (x.map (fun n : ℕ => n.size + 1)).sum + x.length + 1 + 1
  have := maximum_size_le x
  omega

theorem Code.poly_le : Code.le.IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  simp only [Code.eval, Ty.size]
  omega

theorem sum_map_le_length_mul {A : Type} (xs : List A) (f : A → ℕ) (M : ℕ)
    (h : ∀ x ∈ xs, f x ≤ M) : (xs.map f).sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem sum_map_add {A : Type} (xs : List A) (f g : A → ℕ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Code.IsPoly.map {a b : Ty} {f : Code a b} (hf : f.IsPoly) :
    (Code.map f).IsPoly := by
  obtain ⟨C, d, hf⟩ := hf
  refine ⟨C + 2, d + 1, ?_⟩
  intro xs
  let s := (Ty.list a).size xs
  have hlen : xs.length ≤ s := by dsimp [s, Ty.size]; omega
  have heach : ∀ x ∈ xs, f.cost x + b.size (f.eval x) ≤ bound C d s := by
    intro x hx
    exact (hf x).trans (bound_mono le_rfl le_rfl (Ty.size_mem_le hx))
  have hsum := sum_map_le_length_mul xs (fun x => f.cost x + b.size (f.eval x)) _ heach
  rw [sum_map_add] at hsum
  have hsum' := hsum.trans (Nat.mul_le_mul_right (bound C d s) hlen)
  have hone : 1 ≤ (s + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hm1 := Nat.mul_le_mul_right (C * (s + 1) ^ d) (Nat.le_succ s)
  have hm2 := Nat.mul_le_mul_left (2 * (s + 1)) hone
  change ((xs.map f.cost).sum + s + 1) +
    (((xs.map f.eval).map b.size).sum + (xs.map f.eval).length + 1) ≤ _
  simp only [List.map_map, List.length_map, Function.comp_def]
  change ((xs.map f.cost).sum + s + 1) +
    ((xs.map (fun x => b.size (f.eval x))).sum + xs.length + 1) ≤ bound (C + 2) (d + 1) s
  simp only [bound, pow_succ] at hsum' ⊢
  nlinarith

theorem size_flatten_le {a : Ty} (xs : List (List a.Value)) :
    (Ty.list a).size xs.flatten ≤ (Ty.list (.list a)).size xs := by
  induction xs with
  | nil => simp [Ty.size]
  | cons ys xs ih =>
    simp only [List.flatten_cons, Ty.size, List.map_append, List.sum_append,
      List.length_append, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem Code.poly_flatten {a : Ty} : (Code.flatten (a := a)).IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro xs
  exact (size_flatten_le xs).trans (Nat.le_succ _)

theorem Code.poly_cons {a : Ty} : (Code.cons (a := a)).IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro x
  simp only [Code.eval, Ty.size, List.map_cons, List.sum_cons, List.length_cons]
  omega

theorem Code.poly_length {a : Ty} : (Code.length (a := a)).IsPoly := by
  apply Code.poly_of_size_le _ (fun _ => le_rfl)
  intro xs
  have hs : xs.length.size ≤ xs.length + 1 := by
    rw [Nat.size_le]
    exact (Nat.lt_succ_self _).trans_le (Nat.lt_two_pow_self.le)
  simp only [Code.eval, Ty.size]
  omega

theorem Code.IsPoly.branch {a b : Ty} {c : Code a .bool} {f g : Code a b}
    (hc : c.IsPoly) (hf : f.IsPoly) (hg : g.IsPoly) : (Code.branch c f g).IsPoly := by
  obtain ⟨C, d, hc⟩ := hc
  obtain ⟨E, e, hf⟩ := hf
  obtain ⟨F, q, hg⟩ := hg
  refine ⟨C + (E + F) + 1, d + (e + q) + 0, ?_⟩
  intro x
  have hcx : c.cost x ≤ bound C d (a.size x) := (Nat.le_add_right _ _).trans (hc x)
  have hfg := bound_add (hf x) (hg x)
  have hone : 1 ≤ bound 1 0 (a.size x) := by simp [bound]
  have htotal := bound_add (bound_add hcx hfg) hone
  simp only [Nat.add_zero] at htotal
  simp only [Code.cost, Code.eval]
  cases c.eval x <;> simp <;> omega

theorem Code.IsPoly.mapWith {s a b : Ty} {f : Code (.pair s a) b} (hf : f.IsPoly) :
    (Code.mapWith f).IsPoly := by
  obtain ⟨C, d, hf⟩ := hf
  refine ⟨C + 2, d + 1, ?_⟩
  intro x
  let n := (Ty.pair s (.list a)).size x
  have hlen : x.2.length ≤ n := by dsimp [n, Ty.size]; omega
  have heach : ∀ y ∈ x.2, f.cost (x.1, y) + b.size (f.eval (x.1, y)) ≤ bound C d n := by
    intro y hy
    have hpair : (Ty.pair s a).size (x.1, y) ≤ n :=
      Nat.add_le_add_right (Nat.add_le_add_left (Ty.size_mem_le hy) _) _
    exact (hf _).trans (bound_mono le_rfl le_rfl hpair)
  have hsum := sum_map_le_length_mul x.2
    (fun y => f.cost (x.1, y) + b.size (f.eval (x.1, y))) _ heach
  rw [sum_map_add] at hsum
  have hsum' := hsum.trans (Nat.mul_le_mul_right (bound C d n) hlen)
  have hone : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hm1 := Nat.mul_le_mul_right (C * (n + 1) ^ d) (Nat.le_succ n)
  have hm2 := Nat.mul_le_mul_left (2 * (n + 1)) hone
  change ((x.2.map (fun y => f.cost (x.1, y))).sum + n + 1) +
    (((x.2.map (fun y => f.eval (x.1, y))).map b.size).sum +
      (x.2.map (fun y => f.eval (x.1, y))).length + 1) ≤ bound (C + 2) (d + 1) n
  simp only [List.map_map, List.length_map, Function.comp_def]
  simp only [bound, pow_succ] at hsum' ⊢
  nlinarith

-- Keep downstream certificate search at the program-syntax level. Unfolding
-- the semantic cost bound during failed `apply` attempts causes unnecessary
-- normalization of whole interpreters.
attribute [irreducible] Code.IsPoly

end FTC.Hardness.Computation

namespace FTC.Hardness.Complexity

open Computation

/-- YES and NO sets are disjoint. Inputs outside their union are unpromised. -/
structure PromiseProblem (t : Ty) where
  yes : t.Value → Prop
  no : t.Value → Prop
  disjoint : ∀ x, yes x → no x → False

def languageProblem (L : List Bool → Prop) : PromiseProblem (.list .bool) where
  yes := L
  no x := ¬ L x
  disjoint _ hy hn := hn hy

/-- Polynomial-time many-one reduction, with an actual program witness. -/
structure PolyReduction {a b : Ty} (P : PromiseProblem a) (Q : PromiseProblem b) where
  program : Code a b
  polynomial : program.IsPoly
  yes : ∀ x, P.yes x → Q.yes (program.eval x)
  no : ∀ x, P.no x → Q.no (program.eval x)

def PolyReduction.comp {a b c : Ty} {P : PromiseProblem a} {Q : PromiseProblem b}
    {R : PromiseProblem c} (f : PolyReduction P Q) (g : PolyReduction Q R) :
    PolyReduction P R where
  program := .comp f.program g.program
  polynomial := f.polynomial.comp g.polynomial
  yes x hx := g.yes _ (f.yes x hx)
  no x hx := g.no _ (f.no x hx)

/-- Polynomial certificate verification in the explicit bit-cost model. -/
def InNP (L : List Bool → Prop) : Prop :=
  ∃ (verifier : Code (.pair (.list .bool) (.list .bool)) .bool),
    verifier.IsPoly ∧ ∃ C d : ℕ, ∀ x,
      L x ↔ ∃ witness : List Bool,
        witness.length ≤ bound C d x.length ∧ verifier.eval (x, witness) = true

def InP (L : List Bool → Prop) : Prop :=
  ∃ (decider : Code (.list .bool) .bool), decider.IsPoly ∧
    ∀ x, L x ↔ decider.eval x = true

/-- NP-hardness for a promise problem, in the same explicit program model. -/
def NPHard {t : Ty} (P : PromiseProblem t) : Prop :=
  ∀ L : List Bool → Prop, InNP L → Nonempty (PolyReduction (languageProblem L) P)

theorem NPHard.of_reduction {a b : Ty} {P : PromiseProblem a} {Q : PromiseProblem b}
    (hP : NPHard P) (r : PolyReduction P Q) : NPHard Q := by
  intro L hL
  obtain ⟨f⟩ := hP L hL
  exact ⟨f.comp r⟩

def Solves {a : Ty} (p : Code a .bool) (P : PromiseProblem a) : Prop :=
  (∀ x, P.yes x → p.eval x = true) ∧ (∀ x, P.no x → p.eval x = false)

theorem NPHard.inP_of_solver {a : Ty} {P : PromiseProblem a} (hP : NPHard P)
    {p : Code a .bool} (hpoly : p.IsPoly) (hsolve : Solves p P)
    {L : List Bool → Prop} (hL : InNP L) : InP L := by
  classical
  obtain ⟨r⟩ := hP L hL
  refine ⟨.comp r.program p, r.polynomial.comp hpoly, ?_⟩
  intro x
  constructor
  · intro hx
    exact hsolve.1 _ (r.yes x hx)
  · intro hx
    by_contra hn
    have hfalse := hsolve.2 _ (r.no x hn)
    change p.eval (r.program.eval x) = true at hx
    simp [hfalse] at hx

theorem inNP_of_inP {L : List Bool → Prop} (h : InP L) : InNP L := by
  obtain ⟨p, hp, h⟩ := h
  refine ⟨.comp .fst p, Code.poly_fst.comp hp, 0, 0, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨[], by simp [bound], (h x).mp hx⟩
  · rintro ⟨w, _, hw⟩
    exact (h x).mpr hw

end FTC.Hardness.Complexity
