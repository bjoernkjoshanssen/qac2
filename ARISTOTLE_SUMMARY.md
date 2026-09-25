# Summary of changes for run 5f1bac30-505b-40c5-9724-b970a587ad32
I proved in Lean that `A_Q(w) = 2` for every nonempty binary string `w`, which is the conclusion of Theorem `thm:all`. The main theorem is `QuantumAutomatic.AQ_eq_two` in `RequestProject/QuantumAutomatic/Theorem.lean`. The project builds with no `sorry`, and its only axioms are the standard ones (`propext`, `Classical.choice`, `Quot.sound`).

**Definitions** (`RequestProject/QuantumAutomatic/Defs.lean`, following Section 2 and Definition `def:AQ`)
- Binary strings are lists over `Fin 2`.
- `wordMat U z` is `U(z) = U_{z_m}⋯U_{z_1}`, so the first letter acts first. The paper's recursion `U(zb) = U_b U(z)` is proved as `wordMat_append_singleton`.
- `accProb` is `ρ(z) = |⟨e_k|U(z)e_1⟩|²`.
- `IsQuantumWitness` / `HasQuantumWitness` define witnesses using unitaries from `U(d)`, with the initial state `e_1`. The condition `gap(w) > 0` is written as the equivalent "`ρ(z) < ρ(w)` for every `z ≠ w` of the same length", which is equivalent because there are finitely many such `z`.
- `AQ w` is the least dimension that has a witness.

**Main results**
- `AQ_eq_two`: `AQ w = 2` for `w ≠ []`.
- `exists_universal_witness`: the witness part of `thm:all` in its universal form (cf. Remark `rem:universal`). One fixed pair `U₀, U₁` works for all strings: for every `w` there is a unitary `V` such that `(V†U₀V, V†U₁V, k=1)` is a 2-dimensional witness with `ρ(w) = 1`.
- `not_hasQuantumWitness_of_le_one`: Proposition `prop:basic`(1), i.e. there is no witness in dimension ≤ 1.

**How the proof differs from the paper**
- **Different unitary pair.** I didn't formalize lifts of Świerczkowski's free rotations or the SU(2)→SO(3) correspondence (Lemmas `lem:free` and `lem:bloch`). Instead I used an explicit pair `U_b = M_b/√5`, where `M₀ = diag(1+2i, 1−2i)` and `M₁ = [[1,2],[−2,1]]` are Gaussian-integer matrices with determinant 5.
- **Freeness.** The freeness needed for Lemma `lem:comm` is proved by reducing modulo the Gaussian prime `1+2i` (so into `ZMod 5`, sending `i ↦ 2`). A finite check by exhaustion shows that the first letter of a word can be read off its reduced matrix, so distinct words of equal length give distinct matrices (`wordMat_gM_injective`). It follows that `U(z)U(w) ≠ U(w)U(z)` when `z ≠ w`. Lyndon–Schützenberger isn't needed: if `zw = wz` with `|z| = |w|`, comparing the first `|z|` letters already gives `z = w`.
- **Geometric step.** In place of the Bloch-sphere argument, I conjugate by a unitary `V` whose first column is a unit eigenvector of `U(w)`. For a 2×2 unitary `X`, `|X₁₁| = 1` holds exactly when `X` is diagonal. So if some `z ≠ w` also reached probability 1, `U(z)` and `U(w)` would commute, which contradicts the step above.

**Not formalized:** the general "any free pair of rotations, any lifts" version of the theorem statement, and the extension to larger alphabets (Remark `rem:alphabets`).

I couldn't open the linked earlier project, so this work doesn't build on it.

Every declaration has a docstring naming the part of `quantum_note_v2.tex` it formalizes; helper lemmas name the result they support. The Properties table lists the definitions and the three proved results.