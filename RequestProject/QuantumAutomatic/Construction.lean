module

public import RequestProject.QuantumAutomatic.Defs

/-!
# A universal pair of qubit unitaries

This file provides the "free pair" ingredient used in the proof of Theorem `thm:all` of
`quantum_note_v2.tex`.  Instead of Świerczkowski's free pair of rotations (Lemma `lem:free`)
and the `SU(2) → SO(3)` dictionary (Lemma `lem:bloch`), we use an explicit pair of
Gaussian-integer matrices of determinant `5`,
`M₀ = diag(1 + 2i, 1 - 2i)` and `M₁ = [[1, 2], [-2, 1]]`,
and the unitaries `U_b = M_b / √5`.  Reducing modulo the Gaussian prime `1 + 2i`
(i.e. to `ZMod 5`, with `i ↦ 2`) shows that distinct positive words of equal length give
distinct matrices (a mod-`5` "ping-pong" argument), which is all that Lemma `lem:comm` needs.
-/

@[expose] public section

namespace QuantumAutomatic

open Matrix

/-- The paper's recursion `U(z b) = U_b U(z)` (Section 2, "Automata", of
`quantum_note_v2.tex`) holds for `wordMat`. -/
theorem wordMat_append {d : ℕ} {R : Type*} [Semiring R] (U : Fin 2 → Matrix (Fin d) (Fin d) R)
    (z w : List (Fin 2)) : wordMat U (z ++ w) = wordMat U w * wordMat U z := by
  induction z with
  | nil => simp [wordMat]
  | cons b z ih => simp [wordMat, ih, Matrix.mul_assoc]

/-- The recursive definition `U(z) = U_{z_m} U(z_{[1,m-1]})` of Section 2 ("Automata") of
`quantum_note_v2.tex`, stated for `wordMat`. -/
theorem wordMat_append_singleton {d : ℕ} {R : Type*} [Semiring R]
    (U : Fin 2 → Matrix (Fin d) (Fin d) R) (z : List (Fin 2)) (b : Fin 2) :
    wordMat U (z ++ [b]) = U b * wordMat U z := by
  rw [wordMat_append]; simp [wordMat]

/-- Applying a ring homomorphism entrywise commutes with forming `U(z)` (Section 2,
"Automata", of `quantum_note_v2.tex`); auxiliary to the proof of Theorem `thm:all`. -/
theorem wordMat_map {d : ℕ} {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (U : Fin 2 → Matrix (Fin d) (Fin d) R) (z : List (Fin 2)) :
    (wordMat U z).map f = wordMat (fun b => (U b).map f) z := by
  induction z with
  | nil => simp [wordMat]
  | cons b z ih => simp [wordMat, Matrix.map_mul, ih]

namespace Construction

/-- The Gaussian-integer matrices `M₀ = diag(1+2i, 1-2i)`, `M₁ = [[1,2],[-2,1]]`, each of
determinant `5`.  Up to the factor `1/√5` they are the universal pair used for Theorem `thm:all`
of `quantum_note_v2.tex`, replacing the free pair of rotations of Lemma `lem:free`. -/
def gM : Fin 2 → Matrix (Fin 2) (Fin 2) GaussianInt :=
  ![!![⟨1, 2⟩, 0; 0, ⟨1, -2⟩], !![1, 2; -2, 1]]

/-- Reduction modulo the Gaussian prime `1 + 2i`, i.e. `ℤ[i] → ZMod 5`, `i ↦ 2`
(auxiliary; replaces the mod-`3` argument sketched in the proof of Lemma `lem:free` of
`quantum_note_v2.tex`). -/
def red : GaussianInt →+* ZMod 5 :=
  Zsqrtd.lift (⟨2, by decide⟩ : {r : ZMod 5 // r * r = ((-1 : ℤ) : ZMod 5)})

/-- The reductions of `M₀, M₁` modulo `1 + 2i` (auxiliary to Lemma `lem:comm` of
`quantum_note_v2.tex`). -/
def N : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 5) := ![!![0, 0; 0, 2], !![1, 2; 3, 1]]

/-- `N b` is the reduction of `M_b` (auxiliary to Lemma `lem:comm` of `quantum_note_v2.tex`). -/
lemma map_gM (b : Fin 2) : (gM b).map red = N b := by
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [gM, N, red] <;> decide

/-- Kernel vectors of `N 0` and `N 1` (auxiliary to Lemma `lem:comm` of
`quantum_note_v2.tex`). -/
def kv : Fin 2 → (Fin 2 → ZMod 5) := ![![1, 0], ![3, 1]]

/-- Ping-pong invariant: `X` is nonzero and kills the kernel vector of `N c`.  It records
that the first letter of a word can be read off from its matrix modulo `1 + 2i`
(auxiliary to Lemma `lem:comm` of `quantum_note_v2.tex`). -/
def P (c : Fin 2) (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) : Prop := X *ᵥ kv c = 0 ∧ X ≠ 0

/-- Decidability of the ping-pong invariant (auxiliary to Lemma `lem:comm` of
`quantum_note_v2.tex`). -/
instance (c : Fin 2) (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) : Decidable (P c X) := by
  unfold P; infer_instance

/-- Base case of the ping-pong invariant (auxiliary to Lemma `lem:comm` of
`quantum_note_v2.tex`). -/
lemma P_base : ∀ b : Fin 2, P b (N b) := by decide

/-- Inductive step of the ping-pong invariant, checked by exhaustion over `ZMod 5`
(auxiliary to Lemma `lem:comm` of `quantum_note_v2.tex`). -/
lemma P_step' : ∀ (b c : Fin 2) (a e f g : ZMod 5),
    P c !![a, e; f, g] → P b (!![a, e; f, g] * N b) := by decide

/-- The two ping-pong invariants are incompatible, checked by exhaustion over `ZMod 5`
(auxiliary to Lemma `lem:comm` of `quantum_note_v2.tex`). -/
lemma P_sep' : ∀ (a e f g : ZMod 5), P 0 !![a, e; f, g] → P 1 !![a, e; f, g] → False := by
  decide

/-- Eta expansion of a `2 × 2` matrix (auxiliary). -/
lemma eta2 {R : Type*} (X : Matrix (Fin 2) (Fin 2) R) : X = !![X 0 0, X 0 1; X 1 0, X 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Inductive step of the ping-pong invariant (auxiliary to Lemma `lem:comm` of
`quantum_note_v2.tex`). -/
lemma P_step (b c : Fin 2) (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) (h : P c X) :
    P b (X * N b) := by
  rw [eta2 X] at h ⊢; exact P_step' _ _ _ _ _ _ h

/-- The two ping-pong invariants are incompatible (auxiliary to Lemma `lem:comm` of
`quantum_note_v2.tex`). -/
lemma P_sep (X : Matrix (Fin 2) (Fin 2) (ZMod 5)) (h0 : P 0 X) (h1 : P 1 X) : False := by
  rw [eta2 X] at h0 h1; exact P_sep' _ _ _ _ h0 h1

/-- The matrix of a nonempty word, reduced modulo `1 + 2i`, satisfies the ping-pong invariant
of its first letter (auxiliary to Lemma `lem:comm` of `quantum_note_v2.tex`). -/
lemma P_wordMat (b : Fin 2) (z : List (Fin 2)) : P b ((wordMat gM (b :: z)).map red) := by
  induction z generalizing b with
  | nil => simpa [wordMat, map_gM] using P_base b
  | cons c z ih =>
    have := P_step b c _ (ih c)
    simpa [wordMat, Matrix.map_mul, map_gM] using this

/-- `det M_b = 5` (auxiliary to Lemma `lem:comm` of `quantum_note_v2.tex`). -/
lemma det_gM (b : Fin 2) : (gM b).det = 5 := by
  fin_cases b <;> simp [gM, Matrix.det_fin_two] <;> decide

/-- Distinct positive words of equal length give distinct Gaussian-integer matrices.  This
is the freeness input of Lemma `lem:comm` of `quantum_note_v2.tex` (there obtained from
Lemma `lem:free`), for the pair `M₀, M₁`. -/
theorem wordMat_gM_injective (z w : List (Fin 2)) (hl : z.length = w.length)
    (h : wordMat gM z = wordMat gM w) : z = w := by
  induction z generalizing w with
  | nil => cases w with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons b z ih => cases w with
    | nil => simp at hl
    | cons c w =>
      have hb : b = c := by
        by_contra hbc
        have h1 := P_wordMat b z
        have h2 := P_wordMat c w
        rw [h] at h1
        fin_cases b <;> fin_cases c
        · exact hbc rfl
        · exact P_sep _ h1 h2
        · exact P_sep _ h2 h1
        · exact hbc rfl
      subst hb
      have h' : wordMat gM z * gM b = wordMat gM w * gM b := by simpa [wordMat] using h
      have h'' := congrArg (· * (gM b).adjugate) h'
      simp only [Matrix.mul_assoc, Matrix.mul_adjugate, det_gM] at h''
      have h3 : wordMat gM z = wordMat gM w := by
        refine Matrix.ext fun i j => ?_
        have := congrFun (congrFun h'' i) j
        simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul] at this
        exact mul_left_cancel₀ (by decide : (5 : GaussianInt) ≠ 0) this
      rw [ih w (by simpa using hl) h3]

end Construction

end QuantumAutomatic
