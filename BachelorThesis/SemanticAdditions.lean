import Mathlib

namespace FirstOrder
namespace Language
namespace Sentence

universe u v w
variable {L : Language.{u, v}} {φ ψ : L.Sentence} {M : Type w} [L.Structure M]


@[simp]
theorem not_realize_bot : ¬(M ⊨ (⊥ : L.Sentence)) :=
  False.elim

@[simp]
theorem realize_top : M ⊨ (⊤ : L.Sentence) :=
  False.elim

@[simp]
theorem realize_inf : M ⊨ φ ⊓ ψ ↔ M ⊨ φ ∧ M ⊨ ψ :=
  Formula.realize_inf

@[simp]
theorem realize_sup : M ⊨ φ ⊔ ψ ↔ M ⊨ φ ∨ M ⊨ ψ :=
  Formula.realize_sup

@[simp]
theorem realize_imp : M ⊨ φ.imp ψ ↔ M ⊨ φ → M ⊨ ψ :=
  Formula.realize_imp

@[simp]
theorem realize_iff : M ⊨ φ.iff ψ ↔ (M ⊨ φ ↔ M ⊨ ψ) :=
  Formula.realize_iff

end Sentence
end Language
end FirstOrder
