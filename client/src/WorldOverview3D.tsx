import { useEffect, useRef, useState } from 'react';
import { DialoguePhone, type DialogueMessage } from './DialoguePhone';
import type { TutorialStepSource, World } from './gameData';
import { Tutorial, isTutorialDone } from './Tutorial';
import { init } from './worldOverview3DScene';
import './css/WorldOverview3D.css';

const WORLD_OVERVIEW_TUTORIAL_STORAGE_KEY = 'tutorialDone:worldOverview';

type DialogueSpeaker = 'Simplicio' | 'Socrates';

// Replace or extend this array with the full Simplicio-Socrates dialogue.
const WHY_REAL_ANALYSIS_DIALOGUE: DialogueMessage<DialogueSpeaker>[] = [
  {
    speaker: 'Simplicio',
    text: 'Hey Socrates, my old friend! Got a minute?',
  },
  {
    speaker: 'Socrates',
    text: 'Hey Simplicio, sure, what\'s up?',
  },
  {
    speaker: 'Simplicio',
    text: 'What is “Real Analysis”?',
  },
  {
    speaker: 'Socrates',
    text: 'Oh, it\'s just Calculus, but done “right”.',
  },
  {
    speaker: 'Simplicio',
    text: 'Huh? Why does Calculus need a new name? What\'s wrong with it?',
  },
  {
    speaker: 'Socrates',
    text: 'Well, nothing really. Quick: what\'s a derivative?',
  },
  {
    speaker: 'Simplicio',
    kind: 'parts',
    parts: [
      {
        kind: 'text',
        text: String.raw`Easy! If I have a function $f : \mathbb{R} \to \mathbb{R}$ and it's differentiable at $x$, then the derivative is 
$$
f'(x) := \lim_{h \to 0}\frac{f(x+h) - f(x)}{h}.
$$`,
      },
      {
        kind: 'image',
        src: '/images/Deriv.jpg',
        alt: 'The derivative',
        href: 'https://en.wikipedia.org/wiki/Derivative',
      },
      {
        kind: 'text',
        text: String.raw`This represents the “instantaneous” slope of the graph of the function $y=f(x)$ at the point $(x, f(x))$.`,
      },
    ],
  },
  {
    speaker: 'Socrates',
    text: 'Very good! And tell me please, what is an integral?',
  },
  {
    speaker: 'Simplicio',
    kind: 'parts',
    parts: [
      {
        kind: 'text',
        text: String.raw`That's easy, too! It's the area under a curve.`,
      },
      {
        kind: 'image',
        src: '/images/Integral.jpg',
        alt: 'Area under a curve',
        href: 'https://en.wikipedia.org/wiki/Integral',
      },
      {
        kind: 'text',
        text: String.raw`More precisely, if you have a function $f : \mathbb{R} \to \mathbb{R}$, and you want to know the area under the curve of $f$ between $x=a$ and $x=b$, then you pretend that you have infinitely many, infinitely small rectangles, work out their areas as base times height, and add them up:
$$
\int_a^b f(x)dx := \lim_{N\to\infty} \sum_{j=0}^{N-1} \frac{b-a}{N} f\left(a + j\frac{b-a}{N}\right)
$$`,
      },
    ],
  },
  {
    speaker: 'Socrates',
    text: 'Great. And what are the two Fundamental Theorems of Calculus?',
  },
  {
    speaker: 'Simplicio',
    text: [
      String.raw`These too are easy! The first one says that if you make a new function by integrating $f$ up to a variable amount, $x$, that is, let`,
      String.raw`$$
F(x) := \int_a^x f(t)dt,
$$`,
      String.raw`then the derivative of the new function is just`,
      String.raw`$$
F'(x) = f(x).
$$`,
    ].join('\n\n'),
  },
  {
    speaker: 'Socrates',
    text: 'And the second?',
  },
  {
    speaker: 'Simplicio',
    text: [
      String.raw`The second one says that, conversely, if $F$ is an antiderivative of $f$, that is, $F'(x)=f(x)$, then it's easy to work out the area under the curve, because`,
      String.raw`$$
\int_a^b f(x)dx = F(b) - F(a).
$$`,
      'So differentiation and integration are inverse operations!',
    ].join('\n\n'),
  },
  {
    speaker: 'Socrates',
    text: 'Perfect. Now, here\'s the problem. You used words like “limit”, “infinitely many”, “infinitely small”, and so on. What do they *actually* mean?',
  },
  {
    speaker: 'Simplicio',
    text: 'Oh, you know, it\'s when something happens “eventually”. You just have to get used to the feel of it.',
  },
  {
    speaker: 'Socrates',
    kind: 'parts',
    parts: [
      {
        kind: 'text',
        text: 'Hmm yes, I see. I agree that that\'s an OK way to think of it, for a while at least, and one that suited Newton (who was quite uncomfortable with such words), and Leibniz (who was more care-free here), the two 17th century inventors of calculus (if you don\'t count people like the ancient Greeks Eudoxus and Archimedes, or the 14th century Indian Madhava... but this isn\'t a history lesson).',
      },
      {
        kind: 'image',
        src: '/images/People.jpg',
        alt: 'Newton, Leibniz, Eudoxus, Archimedes, Madhava, Bernoulli, and Euler',
        href: 'https://en.wikipedia.org/wiki/History_of_calculus',
      },
      {
        kind: 'text',
        text: 'Leibniz taught the Bernoulli brothers (the world\'s “first AP Calc students”!), who taught, among others, the Marquis de l\'Hopital, and the great Leonhard Euler (the first “Calc native”), who taught the rest of us. All was going quite well... and then came the 19th Century.',
      },
    ],
  },
  {
    speaker: 'Simplicio',
    text: 'Huh? What happened in the 19th Century?',
  },
  {
    speaker: 'Socrates',
    kind: 'parts',
    parts: [
      {
        kind: 'text',
        text: 'Well you see, a guy named Augustin-Louis Cauchy came along (roughly in the 1810s), and started making a fuss that we weren\'t really doing things perfectly “rigorously”. He set out to reprove the theorems of calculus using precise definitions rather than hand-waving.',
      },
      {
        kind: 'image',
        src: '/images/Cauchy.jpg',
        alt: 'Augustin-Louis Cauchy',
        href: 'https://en.wikipedia.org/wiki/Augustin-Louis_Cauchy',
      },
      {
        kind: 'text',
        text: 'He was making great progress, including proving statements like: the limit of continuous functions is continuous.',
      },
    ],
  },
  {
    speaker: 'Simplicio',
    text: 'Sure, that sounds perfectly reasonable. A limit is a continuous process, so you do that to continuous functions, and of course in the end you should get something continuous, too. No?',
  },
  {
    speaker: 'Socrates',
    text: 'Well, the problem is that around the same time, another guy, Joseph Fourier, was going around claiming that he could add up a bunch of sines and cosines, and get basically any function he wants, including, say, the discontinuous sawtooth!',
  },
  {
    speaker: 'Simplicio',
    text: 'What?!',
  },
  {
    speaker: 'Socrates',
    kind: 'parts',
    parts: [
      {
        kind: 'text',
        text: String.raw`Look for yourself: Here's a graph of $\sum_{n=1}^{100}\frac1n \sin(nx)$. As you take $100$ out to infinity, Fourier claims that this will get closer and closer to a sawtooth function!`,
      },
      {
        kind: 'image',
        src: '/images/Fourier.jpg',
        alt: 'Fourier series',
        href: 'https://en.wikipedia.org/wiki/Joseph_Fourier',
      },
    ],
  },
  {
    speaker: 'Simplicio',
    kind: 'parts',
    parts: [
      {
        kind: 'text',
        text: String.raw`Whoa. Wait, I can think of an even easier example: just look at the simplest family of polynomials, $f_n(x) = x^n$, on the unit interval $[0,1]$. When you take high powers of any point strictly less than $1$, that goes to $0$ in the limit, but powers of $1$ itself always stay at $1$.

So the limiting function is discontinuous, too! What the heck is going on here?`,
      },
      {
        kind: 'image',
        src: '/images/Powers.png',
        alt: 'Power functions on the unit interval',
      },
    ],
  },
  {
    speaker: 'Socrates',
    text: 'Very good, Simplicio! Exactly right, between Fourier and Cauchy, they “broke math”. You break it, you buy it!',
  },
  {
    speaker: 'Simplicio',
    text: 'Ok, so what\'s the right answer, how *do* you do calculus rigorously?',
  },
  {
    speaker: 'Socrates',
    text: 'Not so fast! Things got even worse, and by the mid-19th century, people realized that we don\'t even know what the real numbers *are*!',
  },
  {
    speaker: 'Simplicio',
    kind: 'parts',
    parts: [
      {
        kind: 'text',
        text: 'What? What do you mean, what are they? Here they are right here:',
      },
      {
        kind: 'image',
        src: '/images/RealLine.png',
        alt: 'The real number line',
        href: 'https://en.wikipedia.org/wiki/Real_number',
      },
      {
        kind: 'text',
        text: String.raw`There's zero, and one, and $-2$, and $\frac35$, and $\sqrt 2$, and $e$ and $\pi$. What's the problem?`,
      },
    ],
  },
  {
    speaker: 'Socrates',
    text: 'Well, do you remember that you need something called the Intermediate Value Theorem in calculus?',
  },
  {
    speaker: 'Simplicio',
    text: 'Sure, if you have a continuous function, and it goes from being negative to being positive, then it has to cross zero at some point in between.',
  },
  {
    speaker: 'Socrates',
    text: String.raw`Very good. Tell me about the function $f(x) = x^2 - 2$. In particular, what happens to $f$ on the rational numbers?`,
  },
  {
    speaker: 'Simplicio',
    text: String.raw`Ok, well if $x$ is a rational number, then so is $x^2$, and hence so is $x^2-2$. So actually, we could say that $f : \mathbb Q \to \mathbb Q$, that is, $f$ maps rational numbers to rational numbers.

Over the reals, the graph of $y=f(x)$ is a simple parabola. But you'd asked me about the Intermediate Value Theorem. Hmm. When $x=0,$ I know that $f(x)$ will be $f(0)=0^2-2=-2$ which is negative. And when $x=2$, $f(2)=2^2-2=2$ which is positive.`,
  },
  {
    speaker: 'Socrates',
    text: 'Go on...',
  },
  {
    speaker: 'Simplicio',
    text: String.raw`So there's a root of $f$ somewhere between $0$ and $2$. But the place where $f$ crosses the $x$-axis is at $x=\sqrt2\approx 1.41\dots$.`,
  },
  {
    speaker: 'Socrates',
    text: 'And what did the Pythagoreans know about this number?',
  },
  {
    speaker: 'Simplicio',
    text: String.raw`Supposedly one of them, Hippasus, figured out that $\sqrt2$ is irrational, which ruined their entire theory of geometry and form (they originally believed that *all* numbers were rational); legend has it that Hippasus was drowned at sea for his heresy.`,
  },
  {
    speaker: 'Socrates',
    text: 'So...',
  },
  {
    speaker: 'Simplicio',
    text: 'So wait, if we just restrict to rational inputs, then this parabola is negative, and then it\'s positive, and it *never* hits zero?! But there are tons of rational numbers all over the place. So what makes the real numbers different from the rational numbers, so that the Intermediate Value Theorem actually holds?',
  },
  {
    speaker: 'Socrates',
    text: 'Ah! Now, Simplicio, my friend, we are ready to begin.',
  },
];

const WORLD_OVERVIEW_TUTORIAL_STEPS: TutorialStepSource[] = [
  {
    target: '.world-3d-container',
    title: 'Welcome to Real Analysis, The Game!',
    content: 'This tutorial will show you around.',
    placement: 'center',
  },
  {
    target: '.world-3d-why-btn',
    content: 'Want to know what our Course - ahem, Game - is all about? Click here.',
    placement: 'bottom',
  },
  {
    target: '.world-3d-reset-btn',
    content: 'If you want to reset the browser and start all over, click this reset button.',
    placement: 'left',
  },
  {
    target: '.world-3d-help-btn',
    content: 'And if you want to see this tutorial again, just click here.',
    placement: 'left',
  },
  {
    target: '.world-3d-first-world-anchor',
    content: 'When you are ready to play, click on the first world to get started.  Enjoy the game!',
    placement: 'bottom',
  },
];

type Props = {
  worlds: World[];
  onSelectWorld: (worldId: string, levelIndex: number) => void;
};

type HoverInfo = {
  world: World;
  x: number;
  y: number;
} | null;

type ScreenPosition = {
  x: number;
  y: number;
} | null;

export function WorldOverview3D({ worlds, onSelectWorld }: Props) {
  const containerRef = useRef<HTMLDivElement>(null);
  const callbacksRef = useRef({ onSelectWorld });
  callbacksRef.current.onSelectWorld = onSelectWorld;
  const [hover, setHover] = useState<HoverInfo>(null);
  const [runTutorial, setRunTutorial] = useState(false);
  const [showWhy, setShowWhy] = useState(false);
  const [firstWorldPosition, setFirstWorldPosition] = useState<ScreenPosition>(null);

  function clearSavedBrowserState() {
    const ok = window.confirm('Clear saved browser state for this app? This resets tutorial progress and saved settings.');
    if (!ok) return;
    localStorage.clear();
    sessionStorage.clear();
    location.reload();
  }

  useEffect(() => {
    const el = containerRef.current;
    if (!el) return;

    const { dispose } = init(el, worlds, {
      onHover(world, screenX, screenY) {
        if (world) {
          setHover({ world, x: screenX, y: screenY });
        } else {
          setHover(null);
        }
      },
      onSelect(worldId) {
        callbacksRef.current.onSelectWorld(worldId, 0);
      },
      onFirstWorldScreenPosition(screenX, screenY) {
        setFirstWorldPosition({ x: screenX, y: screenY });
      },
    });

    return dispose;
  }, [worlds]);

  useEffect(() => {
    if (isTutorialDone(WORLD_OVERVIEW_TUTORIAL_STORAGE_KEY)) return;
    setRunTutorial(true);
  }, []);

  return (
    <div className="world-3d-container" ref={containerRef}>
      <Tutorial
        run={runTutorial}
        steps={WORLD_OVERVIEW_TUTORIAL_STEPS}
        storageKey={WORLD_OVERVIEW_TUTORIAL_STORAGE_KEY}
        onDone={() => setRunTutorial(false)}
      />
      <div className="world-3d-motivation">
        <button
          className="world-3d-control-btn world-3d-why-btn"
          onClick={() => setShowWhy(true)}
          title="Why real analysis?"
          aria-label="Why real analysis?"
        >
          Why Real Analysis?
        </button>
      </div>
      <div className="world-3d-controls">
        <button
          className="world-3d-control-btn world-3d-help-btn"
          onClick={() => setRunTutorial(true)}
          title="Start tutorial"
          aria-label="Start tutorial"
        >
          ?
        </button>
        <button
          className="world-3d-control-btn world-3d-reset-btn"
          onClick={clearSavedBrowserState}
          title="Clear saved browser state"
          aria-label="Clear saved browser state"
        >
          &#x21BA;
        </button>
      </div>
      {firstWorldPosition && (
        <div
          className="world-3d-first-world-anchor"
          style={{ left: firstWorldPosition.x, top: firstWorldPosition.y }}
        />
      )}
      {hover && (
        <div
          className="world-3d-label"
          style={{ left: hover.x + 16, top: hover.y - 10 }}
        >
          <div className="world-3d-label-name">{hover.world.name}</div>
          {hover.world.description && (
            <div className="world-3d-label-desc">{hover.world.description}</div>
          )}
          <div className="world-3d-label-levels">
            {hover.world.levels.length}{' '}
            {hover.world.levels.length === 1 ? 'level' : 'levels'}
          </div>
        </div>
      )}
      {showWhy && (
        <div className="modal-backdrop" onClick={() => setShowWhy(false)}>
          <div className="modal why-dialogue-modal" onClick={(e) => e.stopPropagation()}>
            <button
              className="modal-close"
              onClick={() => setShowWhy(false)}
              title="Close"
            >&times;</button>
            <div className="modal-body why-dialogue-body">
              <DialoguePhone
                title="Why Real Analysis?"
                localSpeaker="Simplicio"
                remoteSpeaker="Socrates"
                remoteAvatarSrc="https://commons.wikimedia.org/wiki/Special:FilePath/UWASocrates_gobeirne_cropped.jpg"
                remoteAvatarAlt="Bust of Socrates"
                messages={WHY_REAL_ANALYSIS_DIALOGUE}
              />
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
