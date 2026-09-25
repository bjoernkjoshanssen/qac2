module

public import Mathlib

/-!
# Maximum-likelihood quantum automatic complexity: definitions

This file formalizes the objects of Section 2 ("Notation and conventions") of
`quantum_note_v2.tex`, in particular Definition `def:AQ`.

* Binary strings `w ∈ {0,1}^n` are represented as lists `List (Fin 2)`; the length of the
  string is the length of the list, and the first letter `w₁` is the head of the list.
* The standard basis vector `e_j` of `ℂ^d` corresponds to the index `j - 1 : Fin d`, so
  `e₁` is the index `0`.
-/

@[expose] public section

namespace QuantumAutomatic

open Matrix

/-- The operator `U(z)` of Section 2 ("Automata") of `quantum_note_v2.tex`: for letters
`U 0, U 1` and a string `z = z₁ ⋯ z_m`, `wordMat U z = U_{z_m} ⋯ U_{z_2} U_{z_1}`, so that the
*first* letter of `z` acts first (it is the rightmost factor).

The paper defines `U(z)` by recursion on the *last* letter, `U(z) = U_{z_m} U(z_{[1,m-1]})`;
here the (equivalent) recursion is on the *first* letter, `U(b z) = U(z) U_b`.  The paper's
recursion is recovered as `QuantumAutomatic.wordMat_append_singleton`.
We allow an arbitrary coefficient semiring `R` (the paper uses `R = ℂ`). -/
def wordMat {d : ℕ} {R : Type*} [Semiring R] (U : Fin 2 → Matrix (Fin d) (Fin d) R) :
    List (Fin 2) → Matrix (Fin d) (Fin d) R
  | [] => 1
  | b :: z => wordMat U z * U b

/-- The acceptance probability `ρ(z) = |⟨e_k | U(z) e_1⟩|²` of Section 2 ("Automata") of
`quantum_note_v2.tex`.  Here `e₁` is the index of the initial basis state (the formal
witness notion `IsQuantumWitness` requires it to be the first index `0`, i.e. the vector
`e_1` of the paper) and `k` is the accepting index.  Note `⟨e_k | U(z) e_1⟩` is simply the
`(k, e₁)` entry of the matrix `U(z)`. -/
noncomputable def accProb {d : ℕ} (U : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (e₁ k : Fin d)
    (z : List (Fin 2)) : ℝ :=
  Complex.normSq (wordMat U z k e₁)

/-- A `d`-dimensional quantum witness for the string `w` (Definition `def:AQ` of
`quantum_note_v2.tex`): unitaries `U 0, U 1 ∈ U(d)`, the initial state `e₁` (which must be
the first basis vector, index `0`), and an accepting index `k`, such that
`gap(w) = min_{z ∈ {0,1}^n \ {w}} (ρ(w) - ρ(z)) > 0`.

Since `{0,1}^n` is finite, `gap(w) > 0` is equivalent to `ρ(z) < ρ(w)` for every string
`z ≠ w` of the same length `n`, which is the form used here. -/
def IsQuantumWitness {d : ℕ} (w : List (Fin 2)) (U : Fin 2 → unitaryGroup (Fin d) ℂ)
    (e₁ k : Fin d) : Prop :=
  e₁.val = 0 ∧
    ∀ z : List (Fin 2), z.length = w.length → z ≠ w →
      accProb (fun b => (U b : Matrix (Fin d) (Fin d) ℂ)) e₁ k z <
        accProb (fun b => (U b : Matrix (Fin d) (Fin d) ℂ)) e₁ k w

/-- The string `w` admits a `d`-dimensional quantum witness (Definition `def:AQ` of
`quantum_note_v2.tex`). -/
def HasQuantumWitness (d : ℕ) (w : List (Fin 2)) : Prop :=
  ∃ (U : Fin 2 → unitaryGroup (Fin d) ℂ) (e₁ k : Fin d), IsQuantumWitness w U e₁ k

/-- The maximum-likelihood quantum automatic complexity `A_Q(w)` (Definition `def:AQ` of
`quantum_note_v2.tex`): the least dimension `d` admitting a `d`-dimensional quantum witness
for `w`. -/
noncomputable def AQ (w : List (Fin 2)) : ℕ :=
  sInf {d : ℕ | HasQuantumWitness d w}

end QuantumAutomatic
