import ProbingViterbo.Main

namespace ProbingViterbo

def demoMessage : String :=
  s!"Lean says: {hello}"

theorem demoMessage_not_empty : demoMessage ≠ "" := by
  decide

end ProbingViterbo
