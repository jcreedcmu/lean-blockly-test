import { useEffect, useRef, useState } from 'react';
import type { World } from './gameData';
import { init } from './worldOverview3DScene';
import './css/WorldOverview3D.css';

type Props = {
  worlds: World[];
  onSelectWorld: (worldId: string, levelIndex: number) => void;
};

type HoverInfo = {
  world: World;
  x: number;
  y: number;
} | null;

export function WorldOverview3D({ worlds, onSelectWorld }: Props) {
  const containerRef = useRef<HTMLDivElement>(null);
  const [hover, setHover] = useState<HoverInfo>(null);

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
        onSelectWorld(worldId, 0);
      },
    });

    return dispose;
  }, [worlds, onSelectWorld]);

  return (
    <div className="world-3d-container" ref={containerRef}>
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
    </div>
  );
}
