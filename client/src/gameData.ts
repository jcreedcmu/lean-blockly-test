import type { BlocklyState } from './Blockly.tsx';

export type LevelDefinition = {
  name: string;
  initial: BlocklyState;
  allowedBlocks?: string[];
  introduction?: string;
};

export type World = {
  id: string;
  name: string;
  description?: string;
  levels: LevelDefinition[];
  dependsOn: string[];
};

export type GameData = {
  worlds: World[];
};

export type NavigationState =
  | { kind: 'worldOverview' }
  | { kind: 'playing'; worldId: string; levelIndex: number };

const emptyLevel: BlocklyState = {
  blocks: {
    languageVersion: 0,
    blocks: [
      {
        type: 'lemma',
        id: 'placeholder-lemma',
        x: 61,
        y: 61,
        fields: {
          THEOREM_NAME: 'placeholder',
          THEOREM_DECLARATION: ': True',
        },
      },
    ],
  },
};

function makeLevels(worldName: string, count: number): LevelDefinition[] {
  return Array.from({ length: count }, (_, i) => ({
    name: `${worldName} Level ${i + 1}`,
    initial: emptyLevel,
  }));
}

function makeLevelState(theoremName: string, declaration: string): BlocklyState {
  return {
    blocks: {
      languageVersion: 0,
      blocks: [{
        type: 'lemma',
        id: `lemma-${theoremName}`,
        x: 61, y: 61,
        fields: {
          THEOREM_NAME: theoremName,
          THEOREM_DECLARATION: declaration,
        },
      }],
    },
  };
}

const realAnalysisStoryLevels: LevelDefinition[] = [
  {
    name: 'Introduction to Lean',
    initial: makeLevelState('the_problem', '(x : ℝ) (h : x = 5) : x = 5'),
    allowedBlocks: ['prop', 'tactic_apply'],
    introduction: `# Theorem Prover Software

In this course, we will be using a "proof assistant" called Lean. This is software that checks that our proofs prove *exactly* what we claim they prove. It has other really cool pedagogical features that we'll get to later.
It will take a little while to get used to the syntax, so until we're comfortable, we'll intersperse exercises teaching Lean with exercises teaching Real Analysis. Pretty soon all the exercises will just be about Real Analysis.

For this first exercise, we have a hypothesis that we called \`h\` (but we could've called it anything, like \`x_eq_5\`, or \`Alice\`) that says a real number \`x\` equals 5. Our goal is to prove that \`x\` equals 5.
This shouldn't be very hard, but if you don't know the command, you'll be out of luck. Our goal is to prove the same statement as one of the hypotheses.
To solve that goal, the syntax is to write \`apply\`, then a space, and then the name of the hypothesis which matches the goal.`,
  },
  {
    name: 'The rfl tactic',
    initial: makeLevelState('refl_example', '(x y : ℝ) : x ^ 2 + 2 * y = x ^ 2 + 2 * y'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl'],
    introduction: `# When things are identical to themselves

Sometimes in mathematics, we need to prove that something equals itself. For example, we might need to prove that $x ^ 2 + 2 * y = x ^ 2 + 2 * y$.

This isn't quite the same as our previous exercise. There, we had a hypothesis \`h\` that told us \`x = 5\`, and we used \`apply h\` to prove the goal \`x = 5\`.

But now we don't have any hypothesis that says \`x ^ 2 + 2 * y = x ^ 2 + 2 * y\`. We're just being asked to prove that some expression equals itself. We can't say \`apply something\` because there's no \`something\`.

Instead, we will use what mathematicians call the *reflexive property* of equality: everything is equal to itself. In Lean, if you get to a situation where you're trying to prove an equality, and the two things on both sides are *identical*, then the syntax is to give the command \`rfl\` (short for "reflexivity").

Try it out!`,
  },
  {
    name: 'The rewrite tactic',
    initial: makeLevelState('rw_example', '(x y : ℝ) (Bob : x = 2) : x + y = 2 + y'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl', 'tactic_rw'],
    introduction: `# Rewriting with equalities

Now let's learn about rewriting. Suppose you have a hypothesis called \`Bob : x = 2\`, and your goal is to prove that \`x + y = 2 + y\`.

Can you use \`rfl\`? No, because the two sides of the goal (\`x + y\` and \`2 + y\`) are not *identically* the same.

Can you use \`apply Bob\`? No, because \`Bob\` says \`x = 2\`, which is not what the goal is asking for.

But you can use the hypothesis \`Bob\` to *rewrite* the goal. Since \`Bob\` tells us that \`x = 2\`, we can replace \`x\` with \`2\` in our goal.

In Lean, if you have a hypothesis which is an equality, and you want to replace the *left hand side* of that equality with the *right hand side* in your goal, you use the \`rewrite\` tactic. The syntax is:

\`rewrite [hypothesis_name]\`

After you rewrite, you're not done. But you should know how to finish from there.

Try it out!`,
  },
  {
    name: 'The ring_nf tactic',
    initial: makeLevelState('ring_nf_example', '(x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl', 'tactic_rw', 'tactic_ring_nf'],
    introduction: `# Algebraic manipulations

Now let's learn about algebraic simplification. Suppose you need to prove that $(x + y)^3 = x^3 + 3x^2y + 3xy^2 + y^3$.

This is true by the basic laws of algebra - expanding the left side using the distributive law, commutativity, associativity, etc. But doing this by hand would be extremely tedious.

Fortunately, Lean has a powerful tactic called \`ring_nf\` ("ring normal form") that can automatically perform algebraic manipulations like:
- Expanding products
- Collecting like terms
- Rearranging using commutativity and associativity
- Applying the distributive law

When you have an algebraic identity involving addition, subtraction, and multiplication, \`ring_nf\` can often prove it automatically.

Try it out on this classic binomial expansion!`,
  },
  {
    name: 'The use tactic',
    initial: makeLevelState('use_example', '(x y : ℝ) : ∃ (c : ℝ), (x + y)^4 = x^4 + 4*x^3*y + c*x^2*y^2 + 4*x*y^3 + y^4'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl', 'tactic_rw', 'tactic_ring_nf', 'tactic_use'],
    introduction: `# Proving existence

Sometimes in mathematics, you need to prove that something exists. For example, suppose I wanted to ask you what the binomial coefficient in front of $x^2y^2$ is in the expansion of $(x+y)^4$; how would I do it? Lean can't ask questions, it can only prove theorems! So the way I would ask this is: prove that there exists a real number $c$ such that

$(x+y)^4 = x^4 + 4x^3y + cx^2y^2 + 4xy^3 + y^4$.

The way to prove that such a number exists is to exhibit it, that is, tell me which number to *use*, and then prove that that number indeed satisfies the equation.

This is called an *existential statement*. In Lean, as in mathematics, existence is written using \`∃\` (read: "there exists"). This symbol is called the *existential quantifier*.

To prove an existence statement, you need to provide a specific value that works. This is where the \`use\` tactic comes in.

If you think you know what value of \`c\` would work, you can write \`use 42\` (or with \`42\` replaced by whatever number you think is right). Lean will then substitute that value and ask you to prove that the resulting equation is true.

Try writing \`use\`, then a space, and then a number. Do you see what to do after that?`,
  },
  {
    name: 'The intro tactic',
    initial: makeLevelState('intro_example', ' : ∀ (ε : ℝ), ε > 0 → (ε + 1)^2 = (ε + 1)^2'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl', 'tactic_rw', 'tactic_ring_nf', 'tactic_use', 'tactic_intro'],
    introduction: `# Universal statements

In mathematics, we often need to prove statements that are true "for all" values of some variable. For example, we might want to prove: "for all $\\varepsilon > 0$, we have $(\\varepsilon + 1)^2 = (\\varepsilon + 1)^2$."

If you're thinking that \`rfl\` will do the trick, that's a good idea, but it won't work, because the goal isn't (yet) an equality. So we need to do something else first.

In Lean, as in mathematics, "for all" is written using \`∀\`; this is called the *universal quantifier*.

To prove a "for all" statement, you need to show that it's true for an arbitrary element. In Lean, the syntax for this is the command \`intro\`, followed by whatever name you want to give a dummy variable or a hypothesis.

So: when you see a goal that starts with \`∀\`, you can write \`intro\` to "introduce" the variable. For example:
- \`intro ε\` introduces the variable ε. But the goal then changes to: \`ε > 0 → (ε + 1)^2 = (ε + 1)^2\`. So we're not done introducing things.
- Then \`intro hε\` introduces the hypothesis that \`ε > 0\`.

After using \`intro\` twice, the goal will become one that you should know how to solve.

If you want to be really slick, you can combine the two \`intro\` commands into one: \`intro ε hε\`. But don't feel obliged.`,
  },
  {
    name: 'The specialize tactic',
    initial: makeLevelState('specialize_example', '(t : ℝ) (t_pos : t > 0) (f : ℝ → ℝ) (hf : ∀ x > 0, f (x) = x^2) : f (t) = t^2'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl', 'tactic_rw', 'tactic_ring_nf', 'tactic_use', 'tactic_intro', 'tactic_specialize'],
    introduction: `# Using universal statements

Now let's learn the flip side of \`intro\`. You have already learned that:
- if you have \`∃\` in the goal, you write \`use\` to provide a specific value.
- if you have \`∀\` in the goal, you write \`intro\` to introduce an arbitrary variable.

But what if you have \`∀\` in a *hypothesis* and you want to use it for a particular value?

For a concrete example, suppose you have:
- A positive real number \`t\`
- A function \`f : ℝ → ℝ\`
- A hypothesis \`hf : ∀ x > 0, f (x) = x^2\`, meaning "for all x positive, f(x) equals x²"
- And you want to prove the goal \`f (t) = t^2\`.

Can you use \`apply hf\`? No! The hypothesis \`hf\` says "for all positive x, f(x) = x²" but the goal asks specifically about \`f(t) = t²\`. They're not the same.

This is where the \`specialize\` command comes in. You can write \`specialize hf t\` to specialize the statement \`hf\` to the particular value \`t\`. This transforms \`hf\` from "∀ x > 0, f(x) = x²" into "t > 0 → f(t) = t²". You can then write \`specialize hf t_pos\` to use the positivity hypothesis. Or you can kill two birds with one stone via: \`specialize hf t t_pos\`.`,
  },
  {
    name: 'The choose tactic',
    initial: makeLevelState('choose_example', '(f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl', 'tactic_rw', 'tactic_ring_nf', 'tactic_use', 'tactic_intro', 'tactic_specialize', 'tactic_choose'],
    introduction: `# Extracting information from existential quantifiers

Now let's learn the counterpart to \`use\`. You know that if you have \`∃\` in the goal, you write \`use\` to provide a specific value.

But suppose you have a *hypothesis* that says "there exists a real number \`c\` such that \`f(c) = 2\`". In Lean, this looks like:
\`h : ∃ (c : ℝ), f c = 2\`

And say you want to prove that "there exists a real number \`x\` such that \`(f x)^2 = 4\`".

Again, you can't just say \`apply h\` because these are different statements. If you know from \`h\` that at least one such \`c\` exists, how do you *choose* one? The name of this command is... \`choose\`.

The syntax for \`choose\` is as follows:

\`choose c hc using h\`

You need to give a name to both the value of \`c\`, and to the hypothesis with which \`c\` is bundled. Here we named it \`hc\` (a hypothesis about \`c\`).

You should be able to figure out how to solve the goal from here.`,
  },
  {
    name: 'Big Boss',
    initial: makeLevelState('big_boss', '(f : ℝ → ℝ) (h_existential : ∃ (a : ℝ), f (a) = 3) (h_universal : ∀ x > 0, f (x + 1) = f (x) + 9) : ∃ (b : ℝ), ∀ y > 0, f (y + 1)^2 = (f (y) + (f b)^2)^2'),
    allowedBlocks: ['prop', 'tactic_apply', 'tactic_refl', 'tactic_rw', 'tactic_ring_nf', 'tactic_use', 'tactic_intro', 'tactic_specialize', 'tactic_choose'],
    introduction: `# The Final Challenge

Congratulations! You've learned many fundamental tactics for mathematical reasoning in Lean:
- \`apply hypothesisName\` for when a hypothesis matches the goal
- \`rfl\` for reflexivity (proving \`X = X\`)
- \`rewrite [hypothesisName]\` for rewriting using equalities
- \`ring_nf\` for algebraic manipulation
- \`use\` for providing witnesses to existence statements in goals
- \`intro\` for handling universal quantifiers in goals
- \`specialize\` for applying universal statements to specific values in hypotheses
- \`choose value hypothesisOnValue using ExistentialHypothesis\` for extracting information from existence statements in hypotheses

Here's a little "Universal/Existential Quantifier Cheat Sheet":

|           | ∀        | ∃      |
|-----------|----------|--------|
| **Goal**  | \`intro\`    | \`use\`    |
| **Hypothesis** | \`specialize\` | \`choose\` |

Now it's time for your first **Big Boss** - a problem that requires you to use almost ALL of these tactics in a single proof!

Given a function \`f\` and information about its behavior, prove a complex statement that involves existence, universals, algebra, and rewriting. Use everything you've learned.`,
  },
];

export const gameData: GameData = {
  worlds: [
    { id: 'RealAnalysisStory', name: 'The Story of Real Analysis', levels: realAnalysisStoryLevels, dependsOn: [] },
    { id: 'L1Pset', name: 'Pset 1', levels: makeLevels('L1Pset', 5), dependsOn: ['RealAnalysisStory'] },
    { id: 'NewtonsCalculationOfPi', name: "Newton's Computation of π", levels: makeLevels('NewtonsCalculationOfPi', 1), dependsOn: ['RealAnalysisStory'] },
    { id: 'L2Pset', name: 'Pset 2', levels: makeLevels('L2Pset', 2), dependsOn: ['NewtonsCalculationOfPi', 'L1Pset'] },
    { id: 'Lecture3', name: 'More fun with Sequences', levels: makeLevels('Lecture3', 2), dependsOn: ['NewtonsCalculationOfPi'] },
    { id: 'L3Pset', name: 'Pset 3', levels: makeLevels('L3Pset', 4), dependsOn: ['L2Pset'] },
    { id: 'Lecture4', name: 'Even more fun with Sequences', levels: makeLevels('Lecture4', 1), dependsOn: ['L2Pset', 'Lecture3'] },
    { id: 'L4Pset', name: 'Pset 4', levels: makeLevels('L4Pset', 1), dependsOn: ['L3Pset'] },
    { id: 'Lecture5', name: 'Algebraic Limit Theorem, Part I', levels: makeLevels('Lecture5', 1), dependsOn: ['Lecture4', 'L4Pset'] },
    { id: 'Lecture6', name: 'Algebraic Limit Theorem, Part II', levels: makeLevels('Lecture6', 7), dependsOn: ['Lecture5', 'L4Pset'] },
    { id: 'L6Pset', name: 'Pset 6', levels: makeLevels('L6Pset', 5), dependsOn: ['L4Pset'] },
    { id: 'Lecture7', name: 'Algebraic Limit Theorem, Part III', levels: makeLevels('Lecture7', 5), dependsOn: ['Lecture6'] },
    { id: 'L7Pset', name: 'Pset 7', levels: makeLevels('L7Pset', 3), dependsOn: ['L6Pset'] },
    { id: 'Lecture8', name: 'Induction', levels: makeLevels('Lecture8', 1), dependsOn: ['L6Pset', 'L7Pset'] },
    { id: 'L8Pset', name: 'Pset 8', levels: makeLevels('L8Pset', 4), dependsOn: ['L7Pset'] },
    { id: 'Lecture9', name: 'Algebraic Limit Theorem, Part IV', levels: makeLevels('Lecture9', 2), dependsOn: ['L8Pset'] },
    { id: 'L9Pset', name: 'Pset 9', levels: makeLevels('L9Pset', 3), dependsOn: ['L8Pset'] },
    { id: 'Lecture10', name: 'Algebraic Limit Theorem, Part V', levels: makeLevels('Lecture10', 4), dependsOn: ['L9Pset'] },
    { id: 'L10Pset', name: 'Pset 10', levels: makeLevels('L10Pset', 6), dependsOn: ['L9Pset'] },
    { id: 'Lecture11', name: 'The Real Numbers I', levels: makeLevels('Lecture11', 3), dependsOn: ['L9Pset', 'Lecture10', 'L10Pset'] },
    { id: 'L11Pset', name: 'Pset 11', levels: makeLevels('L11Pset', 1), dependsOn: ['Lecture11', 'L10Pset'] },
    { id: 'Lecture12', name: 'Cauchy Sequences II', levels: makeLevels('Lecture12', 4), dependsOn: ['Lecture11', 'L10Pset'] },
    { id: 'L12Pset', name: 'Pset 12', levels: makeLevels('L12Pset', 2), dependsOn: ['Lecture12', 'L11Pset'] },
    { id: 'Lecture13', name: 'Monotone Subsequence', levels: makeLevels('Lecture13', 1), dependsOn: ['L11Pset', 'Lecture12'] },
    { id: 'L13Pset', name: 'Pset 13', levels: makeLevels('L13Pset', 1), dependsOn: ['Lecture13', 'L12Pset'] },
    { id: 'Lecture14', name: 'Bolzano-Weierstrass', levels: makeLevels('Lecture14', 1), dependsOn: ['L12Pset', 'Lecture13'] },
    { id: 'Lecture15', name: 'The Real Numbers', levels: makeLevels('Lecture15', 1), dependsOn: ['Lecture14', 'L13Pset'] },
    { id: 'L15Pset', name: 'Pset 15', levels: makeLevels('L15Pset', 1), dependsOn: ['Lecture15', 'L13Pset'] },
    { id: 'Lecture16', name: 'Series', levels: makeLevels('Lecture16', 1), dependsOn: ['Lecture15'] },
    { id: 'L16Pset', name: 'Pset 16', levels: makeLevels('L16Pset', 3), dependsOn: ['Lecture16', 'L15Pset'] },
    { id: 'Lecture17', name: 'Series II', levels: makeLevels('Lecture17', 4), dependsOn: ['Lecture16', 'L15Pset', 'L16Pset'] },
    { id: 'L17Pset', name: 'Pset 17', levels: makeLevels('L17Pset', 3), dependsOn: ['Lecture17', 'L16Pset'] },
    { id: 'Lecture18', name: 'Infinite Addition', levels: makeLevels('Lecture18', 2), dependsOn: ['Lecture17', 'L16Pset'] },
    { id: 'L18Pset', name: 'Pset 18', levels: makeLevels('L18Pset', 10), dependsOn: ['Lecture18', 'L17Pset', 'L13Pset'] },
    { id: 'Lecture19', name: 'Rearrangements', levels: makeLevels('Lecture19', 4), dependsOn: ['L17Pset', 'L18Pset'] },
    { id: 'Lecture20', name: 'Function Limits', levels: makeLevels('Lecture20', 4), dependsOn: ['L18Pset', 'Lecture19'] },
    { id: 'L20Pset', name: 'Pset 20', levels: makeLevels('L20Pset', 4), dependsOn: ['Lecture20', 'L18Pset'] },
    { id: 'Lecture21', name: 'Function Limits II', levels: makeLevels('Lecture21', 4), dependsOn: ['Lecture20'] },
    { id: 'Lecture22', name: 'Uniformity', levels: makeLevels('Lecture22', 3), dependsOn: ['Lecture21', 'L20Pset'] },
    { id: 'L22Pset', name: 'Pset 22', levels: makeLevels('L22Pset', 4), dependsOn: ['Lecture22', 'L20Pset'] },
    { id: 'Lecture23', name: 'Uniformity II: Continuity', levels: makeLevels('Lecture23', 3), dependsOn: ['Lecture22'] },
    { id: 'Lecture24', name: 'Topology', levels: makeLevels('Lecture24', 5), dependsOn: ['Lecture23', 'L22Pset'] },
    { id: 'L24Pset', name: 'Pset 24', levels: makeLevels('L24Pset', 2), dependsOn: ['Lecture24'] },
    { id: 'Lecture25', name: 'Swapping Limits and Integrals', levels: makeLevels('Lecture25', 2), dependsOn: ['L24Pset', 'Lecture24'] },
  ],
};

export function parseHash(hash: string): NavigationState {
  const match = hash.match(/^#([^/]+)\/(\d+)$/);
  if (match) {
    const worldId = match[1];
    const levelIndex = parseInt(match[2], 10);
    const world = gameData.worlds.find(w => w.id === worldId);
    if (world && levelIndex >= 0 && levelIndex < world.levels.length) {
      return { kind: 'playing', worldId, levelIndex };
    }
  }
  return { kind: 'worldOverview' };
}

export function navToHash(nav: NavigationState): string {
  if (nav.kind === 'playing') return `#${nav.worldId}/${nav.levelIndex}`;
  return '#';
}

/** Topological sort of worlds into rows for DAG layout. */
export function getWorldRows(worlds: World[]): World[][] {
  const worldMap = new Map(worlds.map(w => [w.id, w]));
  const depths = new Map<string, number>();

  function getDepth(id: string): number {
    if (depths.has(id)) return depths.get(id)!;
    const world = worldMap.get(id);
    if (!world || world.dependsOn.length === 0) {
      depths.set(id, 0);
      return 0;
    }
    const maxParent = Math.max(...world.dependsOn.map(getDepth));
    const depth = maxParent + 1;
    depths.set(id, depth);
    return depth;
  }

  worlds.forEach(w => getDepth(w.id));

  const maxDepth = Math.max(...Array.from(depths.values()), 0);
  const rows: World[][] = Array.from({ length: maxDepth + 1 }, () => []);
  worlds.forEach(w => rows[depths.get(w.id)!].push(w));
  return rows;
}
