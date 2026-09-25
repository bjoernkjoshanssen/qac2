module

public import RequestProject.QuantumAutomatic.Construction

/-!
# Theorem `thm:all`: every nonempty binary string has `A_Q(w) = 2`

Formalization of Theorem `thm:all` of `quantum_note_v2.tex` (together with the lower bound
Proposition `prop:basic`(1) that it uses).
-/

public section

namespace QuantumAutomatic

open Matrix Construction

/-- The universal pair of unitaries `U_b = M_b / √5` (`b = 0, 1`), playing the role of the lifts
`U₀, U₁ ∈ SU(2)` of the free pair of rotations in Theorem `thm:all` of `quantum_note_v2.tex`
(cf. Remark `rem:universal`, which gives explicit lifts of Świerczkowski's pair). -/
noncomputable def Uc (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 5 : ℂ)⁻¹) • (gM b).map GaussianInt.toComplex

/-- `U(z) = 5^{-|z|/2} M(z)`: the operator `U(z)` of Section 2 ("Automata") of
`quantum_note_v2.tex` for the universal pair, expressed through the Gaussian-integer word
matrix (auxiliary to the proof of Theorem `thm:all`). -/
lemma wordMat_Uc (z : List (Fin 2)) :
    wordMat Uc z = ((Real.sqrt 5 : ℂ)⁻¹) ^ z.length • (wordMat gM z).map GaussianInt.toComplex := by
  induction z with
  | nil => simp [wordMat]
  | cons b z ih =>
    simp only [wordMat, ih, Uc, Matrix.map_mul, List.length_cons, pow_succ',
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The universal matrices `U₀, U₁` are unitary, i.e. lie in `U(2)` as required in
Theorem `thm:all` of `quantum_note_v2.tex`. -/
lemma Uc_mem (b : Fin 2) : Uc b ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff']
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Uc, gM, mul_apply, Fin.sum_univ_two, Complex.ext_iff, map_ofNat] <;> ring_nf <;> norm_num

/-- Products of unitaries are unitary: `U(z) ∈ U(2)` (Section 2, "Vectors and matrices", of
`quantum_note_v2.tex`). -/
lemma wordMat_Uc_mem (z : List (Fin 2)) : wordMat Uc z ∈ unitaryGroup (Fin 2) ℂ := by
  induction z with
  | nil => exact one_mem _
  | cons b z ih => exact mul_mem ih (Uc_mem b)

/-- Lemma `lem:comm` for the universal pair: distinct strings of equal length give
non-commuting operators. -/
theorem wordMat_Uc_not_comm (z w : List (Fin 2)) (hl : z.length = w.length) (hne : z ≠ w) :
    wordMat Uc z * wordMat Uc w ≠ wordMat Uc w * wordMat Uc z := by
  intro h
  rw [← wordMat_append, ← wordMat_append, wordMat_Uc, wordMat_Uc] at h
  have hs : ((Real.sqrt 5 : ℂ)⁻¹) ^ (w ++ z).length ≠ 0 := by
    apply pow_ne_zero; apply inv_ne_zero; rw [Complex.ofReal_ne_zero]; positivity
  rw [show (z ++ w).length = (w ++ z).length by simp [add_comm]] at h
  have h2 := smul_right_injective _ hs h
  have h3 : wordMat gM (w ++ z) = wordMat gM (z ++ w) :=
    Matrix.map_injective GaussianInt.toComplex_injective h2
  have h4 := wordMat_gM_injective _ _ (by simp [add_comm]) h3
  exact hne ((List.append_inj h4 hl.symm).1).symm

/-- Every `2 × 2` complex matrix can be brought to upper-triangular form by a unitary
conjugation.  This formalizes the step of the proof of Theorem `thm:all` of
`quantum_note_v2.tex` choosing a unit eigenvector `f` of `U(w)` and `V` unitary with
`V e₁ = f` (here `V = [[a, -b̄], [b, ā]]` for `f = (a, b)`). -/
lemma exists_unitary_triangularize (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ V ∈ unitaryGroup (Fin 2) ℂ, (star V * A * V) 1 0 = 0 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hAx : A *ᵥ x = μ • x := by simpa [Matrix.toLin'_apply] using hx.apply_eq_smul
  have hx0 : x ≠ 0 := hx.2
  set r : ℝ := Complex.normSq (x 0) + Complex.normSq (x 1) with hr_def
  have hr : 0 < r := by
    by_contra h
    push_neg at h
    have h0 := Complex.normSq_nonneg (x 0)
    have h1 := Complex.normSq_nonneg (x 1)
    have e0 : x 0 = 0 := Complex.normSq_eq_zero.mp (le_antisymm (by linarith) h0)
    have e1 : x 1 = 0 := Complex.normSq_eq_zero.mp (le_antisymm (by linarith) h1)
    apply hx0
    ext i
    fin_cases i <;> simp [e0, e1]
  set c : ℂ := (((Real.sqrt r)⁻¹ : ℝ) : ℂ) with hc_def
  have hc : c * c = ((r⁻¹ : ℝ) : ℂ) := by
    rw [hc_def, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hr.le]
  have hcc : (starRingEnd ℂ) c = c := Complex.conj_ofReal _
  have e : (starRingEnd ℂ) (x 0) * x 0 + (starRingEnd ℂ) (x 1) * x 1 = (r : ℂ) := by
    rw [hr_def]; push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  set a := x 0 * c with ha
  set b := x 1 * c with hb
  have hab : (starRingEnd ℂ) a * a + (starRingEnd ℂ) b * b = 1 := by
    rw [ha, hb, map_mul, map_mul, hcc]
    calc _ = ((starRingEnd ℂ) (x 0) * x 0 + (starRingEnd ℂ) (x 1) * x 1) * (c * c) := by ring
      _ = 1 := by rw [e, hc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one]
  have h0 : A 0 0 * x 0 + A 0 1 * x 1 = μ * x 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hAx 0
  have h1 : A 1 0 * x 0 + A 1 1 * x 1 = μ * x 1 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun hAx 1
  refine ⟨!![a, -(starRingEnd ℂ) b; b, (starRingEnd ℂ) a], ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
    · linear_combination hab
    · ring
    · ring
    · linear_combination hab
  · simp [mul_apply, Fin.sum_univ_two, ha, hb]
    linear_combination (c * c) * (x 0 * h1 - x 1 * h0)

/-- For a `2 × 2` unitary `X`, the first column is a unit vector:
`|X₁₁|² + |X₂₁|² = 1`.  This is the "equality case of Cauchy–Schwarz" step in the proof of
Theorem `thm:all` of `quantum_note_v2.tex`, specialized to the basis vector `e₁`. -/
lemma normSq_col (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ unitaryGroup (Fin 2) ℂ) :
    Complex.normSq (X 0 0) + Complex.normSq (X 1 0) = 1 := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hX) 0) 0
  simp only [mul_apply, Fin.sum_univ_two, star_apply, one_apply_eq, RCLike.star_def] at h
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  exact h

/-- For a `2 × 2` unitary `X`, the first row is a unit vector: `|X₁₁|² + |X₁₂|² = 1`
(auxiliary to the proof of Theorem `thm:all` of `quantum_note_v2.tex`). -/
lemma normSq_row (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ unitaryGroup (Fin 2) ℂ) :
    Complex.normSq (X 0 0) + Complex.normSq (X 0 1) = 1 := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff.mp hX) 0) 0
  simp only [mul_apply, Fin.sum_univ_two, star_apply, one_apply_eq, RCLike.star_def] at h
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  linear_combination h

/-- Theorem `thm:all` of `quantum_note_v2.tex` (witness part, universal form): there is a single
pair of `2 × 2` unitaries `U₀, U₁` (independent of `w`) such that for every binary string `w`
there is a unitary `V` for which `(V† U₀ V, V† U₁ V, k = 1)` is a `2`-dimensional quantum
witness for `w`, with `ρ(w) = 1`.

The pair used here is `U_b = M_b / √5` with `M₀ = diag(1+2i, 1-2i)`, `M₁ = [[1,2],[-2,1]]`,
instead of lifts of Świerczkowski's free pair of rotations; what is used about it is exactly
the conclusion of Lemma `lem:comm` (`wordMat_Uc_not_comm`). -/
theorem exists_universal_witness :
    ∃ U : Fin 2 → unitaryGroup (Fin 2) ℂ, ∀ w : List (Fin 2),
      ∃ V ∈ unitaryGroup (Fin 2) ℂ, ∃ hV : ∀ b, star V * (U b : Matrix (Fin 2) (Fin 2) ℂ) * V ∈
          unitaryGroup (Fin 2) ℂ,
        IsQuantumWitness w (fun b => ⟨_, hV b⟩) 0 0 ∧
        accProb (fun b => star V * (U b : Matrix (Fin 2) (Fin 2) ℂ) * V) 0 0 w = 1 := by
  refine ⟨fun b => ⟨Uc b, Uc_mem b⟩, fun w => ?_⟩
  obtain ⟨V, hV, hV10⟩ := exists_unitary_triangularize (wordMat Uc w)
  have hsV : star V * V = 1 := mem_unitaryGroup_iff'.mp hV
  have hVs : V * star V = 1 := mem_unitaryGroup_iff.mp hV
  have hmem : ∀ b, star V * Uc b * V ∈ unitaryGroup (Fin 2) ℂ := fun b =>
    mul_mem (mul_mem (Unitary.star_mem hV) (Uc_mem b)) hV
  refine ⟨V, hV, hmem, ?_⟩
  -- the conjugated operators
  set X : List (Fin 2) → Matrix (Fin 2) (Fin 2) ℂ := fun z => star V * wordMat Uc z * V
    with hX_def
  have hconj : ∀ z, wordMat (fun b => star V * Uc b * V) z = X z := by
    intro z
    induction z with
    | nil => simp [wordMat, hX_def, hsV]
    | cons b z ih =>
      simp only [wordMat, ih, hX_def]
      calc star V * wordMat Uc z * V * (star V * Uc b * V)
          = star V * wordMat Uc z * (V * star V) * Uc b * V := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hVs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hXmem : ∀ z, X z ∈ unitaryGroup (Fin 2) ℂ := fun z =>
    mul_mem (mul_mem (Unitary.star_mem hV) (wordMat_Uc_mem z)) hV
  have hW : ∀ z, wordMat Uc z = V * X z * star V := by
    intro z
    rw [hX_def]
    calc wordMat Uc z = (V * star V) * wordMat Uc z * (V * star V) := by
          rw [hVs, Matrix.mul_one, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hacc : ∀ z, accProb (fun b => star V * ((⟨Uc b, Uc_mem b⟩ :
      unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * V) 0 0 z =
      Complex.normSq (X z 0 0) := by
    intro z
    simp only [accProb]
    rw [hconj z]
  have hw00 : Complex.normSq (X w 0 0) = 1 := by
    have := normSq_col (X w) (hXmem w)
    rw [show X w 1 0 = 0 from hV10] at this
    simpa using this
  have hw01 : X w 0 1 = 0 := by
    have := normSq_row (X w) (hXmem w)
    rw [hw00] at this
    exact Complex.normSq_eq_zero.mp (by linarith)
  refine ⟨⟨rfl, fun z hl hne => ?_⟩, by rw [hacc]; exact hw00⟩
  change accProb (fun b => star V * Uc b * V) 0 0 z < accProb (fun b => star V * Uc b * V) 0 0 w
  rw [hacc, hacc, hw00]
  by_contra hle
  push_neg at hle
  have hc := normSq_col (X z) (hXmem z)
  have hr := normSq_row (X z) (hXmem z)
  have hz10 : X z 1 0 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [Complex.normSq_nonneg (X z 1 0)])
  have hz01 : X z 0 1 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith [Complex.normSq_nonneg (X z 0 1)])
  have hcomm : X z * X w = X w * X z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, hz10, hz01, hw01, show X w 1 0 = 0 from hV10] <;> ring
  apply wordMat_Uc_not_comm z w hl hne
  rw [hW z, hW w]
  calc V * X z * star V * (V * X w * star V) = V * X z * (star V * V) * X w * star V := by
        simp only [Matrix.mul_assoc]
    _ = V * (X z * X w) * star V := by rw [hsV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = V * (X w * X z) * star V := by rw [hcomm]
    _ = V * X w * (star V * V) * X z * star V := by
        rw [hsV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Every binary string admits a `2`-dimensional quantum witness (Theorem `thm:all` of
`quantum_note_v2.tex`, the upper bound `A_Q(w) ≤ 2`). -/
theorem hasQuantumWitness_two (w : List (Fin 2)) : HasQuantumWitness 2 w := by
  obtain ⟨U, hU⟩ := exists_universal_witness
  obtain ⟨V, -, hV, hw, -⟩ := hU w
  exact ⟨_, 0, 0, hw⟩

/-- Proposition `prop:basic`(1) of `quantum_note_v2.tex`: a nonempty string has no quantum
witness of dimension `d ≤ 1`, i.e. `A_Q(w) ≥ 2`. -/
theorem not_hasQuantumWitness_of_le_one (w : List (Fin 2)) (hw : w ≠ []) (d : ℕ) (hd : d ≤ 1) :
    ¬ HasQuantumWitness d w := by
  rintro ⟨U, e₁, k, -, hlt⟩
  interval_cases d
  · exact e₁.elim0
  · -- in dimension one every string is accepted with probability one
    have hmem : ∀ z, wordMat (fun b => (U b : Matrix (Fin 1) (Fin 1) ℂ)) z ∈
        unitaryGroup (Fin 1) ℂ := by
      intro z
      induction z with
      | nil => exact one_mem _
      | cons b z ih => exact mul_mem ih (U b).2
    have hone : ∀ z, accProb (fun b => (U b : Matrix (Fin 1) (Fin 1) ℂ)) e₁ k z = 1 := by
      intro z
      have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp (hmem z)) 0) 0
      simp only [mul_apply, Fin.sum_univ_one, star_apply, one_apply_eq, RCLike.star_def] at h
      rw [Subsingleton.elim e₁ 0, Subsingleton.elim k 0]
      apply Complex.ofReal_injective
      rw [accProb, Complex.normSq_eq_conj_mul_self]
      simpa using h
    obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hw
    have := hlt ((b + 1) :: t) (by simp) (by
      simp only [ne_eq, List.cons.injEq, not_and]
      intro h; exfalso; fin_cases b <;> simp at h)
    rw [hone, hone] at this
    exact lt_irrefl _ this

/-- **Theorem `thm:all`** of `quantum_note_v2.tex`: `A_Q(w) = 2` for every nonempty binary
string `w`. -/
theorem AQ_eq_two (w : List (Fin 2)) (hw : w ≠ []) : AQ w = 2 := by
  have h2 : 2 ∈ {d : ℕ | HasQuantumWitness d w} := hasQuantumWitness_two w
  refine le_antisymm (Nat.sInf_le h2) (le_csInf ⟨2, h2⟩ fun d hd => ?_)
  by_contra h
  exact not_hasQuantumWitness_of_le_one w hw d (by omega) hd

end QuantumAutomatic
