import { useEffect, useRef, useState } from 'react';
import type { World } from './gameData';
import { Modal } from './Modal';
import { Tutorial, isTutorialDone } from './Tutorial';
import { WhyRealAnalysisDialogue } from './WhyRealAnalysisDialogue';
import { init } from './worldOverview3DScene';
import worldOverviewTutorial from './levels/worldOverviewTutorial';
import './css/WorldOverview3D.css';

const WORLD_OVERVIEW_TUTORIAL_STORAGE_KEY = 'tutorialDone:worldOverview';

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
        steps={worldOverviewTutorial}
        storageKey={WORLD_OVERVIEW_TUTORIAL_STORAGE_KEY}
        onDone={() => setRunTutorial(false)}
      />
      <button
        className="navbar-btn world-3d-why-btn"
        style={{ position: 'absolute', top: 12, left: 12, zIndex: 20 }}
        onClick={() => setShowWhy(true)}
      >
        Why Real Analysis?
      </button>
      <div className="world-3d-controls">
        <button
          className="navbar-btn world-3d-help-btn"
          onClick={() => setRunTutorial(true)}
          title="Start tutorial"
          aria-label="Start tutorial"
        >
          ?
        </button>
        <button
          className="navbar-btn world-3d-reset-btn"
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
        <Modal onClose={() => setShowWhy(false)}>
          <WhyRealAnalysisDialogue />
        </Modal>
      )}
    </div>
  );
}
