import type { TutorialStep } from '../../gameData';

const tutorial: TutorialStep[] = [
  {
    target: ".goals-panel",
    content: "Look at the goal: the left side and right side are exactly the same expression.",
    placement: "left",
  },
  {
    target: ".blocklyToolbox",
    content: "For a goal where something equals itself, use the rfl tactic. Drag rfl into the theorem block.",
    placement: "right",
  },
  {
    target: ".proof-status",
    content: "Once rfl is in place, Lean should recognize the proof as complete.",
    placement: "left",
  },
];

export default tutorial;
