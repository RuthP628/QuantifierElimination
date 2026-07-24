import Mathlib
import BachelorThesis.SeparatingTypes

set_option linter.style.whitespace false

open FirstOrder Language Formula

universe u v w w'
variable {L : Language} (M : Type w) (N : Type w')
variable [L.Structure M] [L.Structure N]

namespace FirstOrder
namespace Language
namespace Theory

section EmbeddingTests

#check PartialEquiv


end EmbeddingTests

end Theory
end Language
end FirstOrder
