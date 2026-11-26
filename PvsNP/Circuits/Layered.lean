module

public import Init.Data.List.FinRange
public import Init.Data.List.Lemmas

/-! # Boolean expressions and layered circuits

Each layer computes several Boolean expressions from the preceding wires.
The layer outputs are shared, so composing layers adds their gate costs.
-/

@[expose] public section

namespace PvsNP.Circuits

/-- A Boolean expression with constants and gates of fan-in at most two. -/
inductive Expr (α : Type) where
  | const (value : Bool)
  | input (wire : α)
  | not (e : Expr α)
  | and (left right : Expr α)
  | or (left right : Expr α)

namespace Expr

variable {α β : Type}

/-- Evaluate an expression on the given wire values. -/
def eval (x : α → Bool) : Expr α → Bool
  | .const b => b
  | .input i => x i
  | .not e => !(eval x e)
  | .and l r => eval x l && eval x r
  | .or l r => eval x l || eval x r

/-- Count all expression nodes, including references to existing wires. -/
def size : Expr α → Nat
  | .const _ | .input _ => 1
  | .not e => e.size + 1
  | .and l r | .or l r => l.size + r.size + 1

/-- Change the names of input wires without changing the gates. -/
def rename (f : α → β) : Expr α → Expr β
  | .const b => .const b
  | .input i => .input (f i)
  | .not e => .not (rename f e)
  | .and l r => .and (rename f l) (rename f r)
  | .or l r => .or (rename f l) (rename f r)

@[simp] theorem eval_rename (f : α → β) (x : β → Bool) (e : Expr α) :
    (e.rename f).eval x = e.eval (x ∘ f) := by
  induction e <;> simp [rename, eval, Function.comp_def, *]

@[simp] theorem size_rename (f : α → β) (e : Expr α) : (e.rename f).size = e.size := by
  induction e <;> simp [rename, size, *]

/-- The disjunction of a list of expressions built from binary OR gates. -/
def any : List (Expr α) → Expr α
  | [] => .const false
  | e :: es => .or e (any es)

@[simp] theorem eval_any (x : α → Bool) (es : List (Expr α)) :
    (any es).eval x = es.any (eval x) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [any, eval, ih]

theorem eval_any_eq_true (x : α → Bool) (es : List (Expr α)) :
    (any es).eval x = true ↔ ∃ e ∈ es, e.eval x = true := by
  rw [eval_any, List.any_eq_true]

theorem size_any_le (es : List (Expr α)) (B : Nat) (h : ∀ e ∈ es, e.size ≤ B) :
    (any es).size ≤ es.length * (B + 1) + 1 := by
  induction es with
  | nil => simp [any, size]
  | cons e es ih =>
    have he := h e (List.mem_cons_self ..)
    have hs := ih (fun g hg ↦ h g (List.mem_cons_of_mem _ hg))
    simp only [any, size, List.length_cons, Nat.succ_mul]
    omega

end Expr

/-- A layer describes each output wire by an expression on the input wires. -/
abbrev Layer (n m : Nat) := Fin m → Expr (Fin n)

namespace Layer

variable {n m : Nat}

def eval (l : Layer n m) (x : Fin n → Bool) : Fin m → Bool := fun i ↦ (l i).eval x

/-- Total expression size of a layer. -/
def size (l : Layer n m) : Nat := ((List.finRange m).map fun i ↦ (l i).size).sum

theorem size_le_of_forall (l : Layer n m) (B : Nat) (h : ∀ j, (l j).size ≤ B) :
    l.size ≤ m * B := by
  have bound (xs : List (Fin m)) : (xs.map fun j ↦ (l j).size).sum ≤ xs.length * B := by
    induction xs with
    | nil => simp
    | cons j xs ih =>
      have hj := h j
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  simpa only [size, List.length_finRange] using bound (List.finRange m)

end Layer

/-- A circuit with shared wires between adjacent layers. -/
inductive Layered : Nat → Nat → Type where
  | id (n : Nat) : Layered n n
  | cons {n m k : Nat} (layer : Layer n m) (rest : Layered m k) : Layered n k

namespace Layered

variable {n m k : Nat}

/-- Evaluate a circuit by passing each layer's output wires to the next layer. -/
def eval : {n m : Nat} → Layered n m → (Fin n → Bool) → Fin m → Bool
  | _, _, .id _, x => x
  | _, _, .cons l rest, x => rest.eval (l.eval x)

/-- Count expression nodes across all layers, charging shared outputs once. -/
def size : {n m : Nat} → Layered n m → Nat
  | _, _, .id _ => 0
  | _, _, .cons l rest => l.size + rest.size

/-- Connect the output wires of the first circuit to the second circuit's inputs. -/
def append : {n m k : Nat} → Layered n m → Layered m k → Layered n k
  | _, _, _, .id _, q => q
  | _, _, _, .cons l rest, q => .cons l (rest.append q)

@[simp] theorem eval_append (p : Layered n m) (q : Layered m k) (x : Fin n → Bool) :
    (p.append q).eval x = q.eval (p.eval x) := by
  induction p with
  | id => rfl
  | cons l rest ih => exact ih q (l.eval x)

@[simp] theorem size_append (p : Layered n m) (q : Layered m k) :
    (p.append q).size = p.size + q.size := by
  induction p with
  | id => simp [append, size]
  | cons l rest ih => simp [append, size, ih, Nat.add_assoc]

/-- Use the same layer successively for the given number of steps. -/
def repeatLayer (l : Layer n n) : Nat → Layered n n
  | 0 => .id n
  | t + 1 => .cons l (repeatLayer l t)

@[simp] theorem eval_repeatLayer_zero (l : Layer n n) (x : Fin n → Bool) :
    (repeatLayer l 0).eval x = x := rfl

theorem eval_repeatLayer_succ (l : Layer n n) (t : Nat) (x : Fin n → Bool) :
    (repeatLayer l (t + 1)).eval x = l.eval ((repeatLayer l t).eval x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => exact ih (l.eval x)

@[simp] theorem size_repeatLayer (l : Layer n n) (t : Nat) :
    (repeatLayer l t).size = t * l.size := by
  induction t with
  | zero => simp [repeatLayer, size]
  | succ t ih => simp [repeatLayer, size, ih, Nat.succ_mul, Nat.add_comm]

end Layered

end PvsNP.Circuits
