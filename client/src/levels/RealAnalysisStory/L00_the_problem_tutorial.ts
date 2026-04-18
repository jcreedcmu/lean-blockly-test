import type { TutorialStep } from '../../gameData';

const tutorial: TutorialStep[] = [
  {
    target: ".tutorial-workspace-anchor",
    spotlightTarget: ".blocklySvg",
    title: "Welcome to Formal Theorem Proving with Blocks!",
    content: "In this Game, every Level is an Escape Room: you move on when you've solved the Goal. Some will be easier than others. In this Tutorial World, we'll learn the basic language of formal theorem proving. This open workspace is called the Field. You'll drag Tactic Blocks here, fill them with Objects and Assumptions, and then snap the completed blocks into the Main Block to build your proof. Let's get started!",
    placement: "bottom",
    offset: -50,
  },
  {
    target: ".lemma-block",
    title: "Read the Statement",
    content: "The Main Block tells you what you're trying to prove, whether it's a named Theorem or just an Example. In this particular Level, you are given a real number $x$, and an assumption, called `h`, that $x = 5$. Your Goal is to prove that $x = 5$. Yes, you read that right; this can't be too hard. But how exactly do you do it? Let's see.",
    placement: "bottom",
  },
  {
    target: ".goals-panel",
    title: "Watch the Game Board",
    content: "The Game Board on the right shows your current Proof State. At the start, it matches the Main Block: the same Objects, Assumptions, and Goal. As the game progresses, you'll add ever more complicated \"Tactic Blocks\" to the Main Block, and the Game Board will update after each move. Think of the analogy to chess: the Main Block records moves, like algebraic notation, `1. e4 e5 2. Nf3 Nf6`; meanwhile, the Game Board shows the actual positions those moves create. You'll soon get most of your information from the Game Board.",
    placement: "left",
  },
  {
    target: ".tutorial-tactics-category-label",
    title: "Find your Tactics",
    content: "Your Tactic Blocks live on the left. Click `Tactics` to open the Tactic Palette. This tutorial will continue once the tab is open.",
    placement: "right",
    conditions: [{
      kind: "elementExists",
      selector: ".blocklyFlyout [data-id=\"tutorial-toolbox-apply\"]",
      visible: true,
    }],
    advanceDelayMs: 900,
  },
  {
    target: ".blocklyFlyout [data-id=\"tutorial-toolbox-apply\"]",
    title: "Drag apply into the Field",
    content: "Drag `apply` out into the middle of the workspace, but don't snap it into the Main Block yet. First we'll fill in what apply should use. The tutorial will continue once `apply` is on the Field.",
    placement: "right",
    targetWaitTimeout: 5000,
    skipScroll: true,
    actions: [{ kind: 'openToolboxCategory', category: 'Tactics' }],
    conditions: [{
      kind: "workspaceHasBlock",
      block: { type: "tactic_apply" },
    }],
  },
  {
    target: ".tutorial-hyp-h",
    title: "Drag out h",
    content: "On the Game Board, find the assumption named h. Drag just the name h into the empty slot on the apply block. The tutorial will continue once apply contains h.",
    placement: "left",
    conditions: [{
      kind: "workspaceHasBlock",
      block: {
        type: "tactic_apply",
        inputs: {
          ARG: {
            type: "prop",
            fields: { PROP_NAME: "h" },
          },
        },
      },
    }],
  },
  {
    target: ".tutorial-workspace-anchor",
    spotlightTarget: ".game-area",
    title: "Snap the proof together",
    content: "Now snap the completed apply h block into the proof area inside the theorem block. That tells Lean to prove the goal using the matching assumption h.",
    placement: "bottom",
    conditions: [{
      kind: "workspaceHasBlock",
      location: "theoremProof",
      block: {
        type: "tactic_apply",
        inputs: {
          ARG: {
            type: "prop",
            fields: { PROP_NAME: "h" },
          },
        },
      },
    }],
  },
  {
    target: ".proof-status",
    title: "Check your proof",
    content: "Lean is checking your blocks. When they prove the theorem, this status turns green and the tutorial will continue.",
    placement: "left",
    conditions: [{ kind: "proofComplete" }],
  },
  {
    target: ".navbar-info-btn",
    content: "The Info button reopens the lesson text for this level.",
    placement: "bottom",
  },
  {
    target: ".navbar-reset-btn",
    content: "Reset level clears this workspace and puts the theorem back at the start.",
    placement: "bottom",
  },
  {
    target: ".navbar-tutorial-btn",
    content: "The question mark starts this tutorial again.",
    placement: "bottom",
  },
  {
    target: ".navbar-back-btn",
    content: "Back returns to the world map.",
    placement: "bottom",
  },
];

export default tutorial;
