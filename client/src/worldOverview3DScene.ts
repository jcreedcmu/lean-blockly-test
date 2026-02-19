import * as THREE from 'three';
import { CSS2DRenderer, CSS2DObject } from 'three/examples/jsm/renderers/CSS2DRenderer.js';
import { Line2 } from 'three/examples/jsm/lines/Line2.js';
import { LineGeometry } from 'three/examples/jsm/lines/LineGeometry.js';
import { LineMaterial } from 'three/examples/jsm/lines/LineMaterial.js';
import type { World } from './gameData';
import { getWorldRows } from './gameData';

const PALETTE = [
  0xdd3333, 0x33bb33, 0x3333dd,
  0xddaa33, 0xaa33dd, 0x33dddd,
  0xdd6633, 0x66dd33, 0x3366dd,
];

const SPACING_X = 5;
const SPACING_Z = 5;

export type SceneCallbacks = {
  onHover: (world: World | null, screenX: number, screenY: number) => void;
  onSelect: (worldId: string) => void;
};

export function init(
  container: HTMLElement,
  worlds: World[],
  _callbacks: SceneCallbacks,
): { dispose: () => void } {
  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0xffffff);

  const width = container.clientWidth;
  const height = container.clientHeight;

  const camera = new THREE.PerspectiveCamera(50, width / height, 0.1, 200);
  camera.position.set(10, 15, 30);

  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setSize(width, height);
  renderer.setPixelRatio(window.devicePixelRatio);
  container.appendChild(renderer.domElement);

  // --- CSS2D label renderer ---
  const labelRenderer = new CSS2DRenderer();
  labelRenderer.setSize(width, height);
  labelRenderer.domElement.style.position = 'absolute';
  labelRenderer.domElement.style.top = '0';
  labelRenderer.domElement.style.left = '0';
  labelRenderer.domElement.style.pointerEvents = 'none';
  container.appendChild(labelRenderer.domElement);

  scene.add(new THREE.AmbientLight(0xffffff, 0.4));
  const dirLight = new THREE.DirectionalLight(0xffffff, 4.0);
  dirLight.position.set(5, 8, 3);
  scene.add(dirLight);

  // --- Build world cube rings ---
  const rows = getWorldRows(worlds);
  const BIG_CUBE_SIZE = 1;
  const SMALL_CUBE_SIZE = 0.2;
  const RING_SPACING = 0.8; // distance from big cube center to ring of small cubes
  const bigGeo = new THREE.BoxGeometry(BIG_CUBE_SIZE, BIG_CUBE_SIZE, BIG_CUBE_SIZE);
  const smallGeo = new THREE.BoxGeometry(SMALL_CUBE_SIZE, SMALL_CUBE_SIZE, SMALL_CUBE_SIZE);
  const annulusMat = new THREE.MeshBasicMaterial({ color: 0xbbbbbb, side: THREE.DoubleSide });
  const worldToGroup = new Map<string, THREE.Group>();
  const spinners: { mesh: THREE.Mesh; axis: THREE.Vector3; speed: number }[] = [];
  const orbiters: { group: THREE.Group; speed: number }[] = [];

  const totalRows = rows.length;
  const centerX = 0;
  const centerZ = ((totalRows - 1) * SPACING_Z) / 2;

  rows.forEach((row, ri) => {
    const rowWidth = (row.length - 1) * SPACING_X;
    row.forEach((world, ci) => {
      const group = new THREE.Group();
      group.position.set(
        ci * SPACING_X - rowWidth / 2,
        0,
        ri * SPACING_Z,
      );
      scene.add(group);
      worldToGroup.set(world.id, group);

      const n = world.levels.length;
      const colorIndex = worlds.indexOf(world) % PALETTE.length;
      const mat = new THREE.MeshStandardMaterial({ color: PALETTE[colorIndex] });

      // Big center cube
      const bigMesh = new THREE.Mesh(bigGeo, mat);
      group.add(bigMesh);
      {
        const axis = new THREE.Vector3(
          Math.random() - 0.5,
          Math.random() - 0.5,
          Math.random() - 0.5,
        ).normalize();
        const speed = (0.3 + Math.random() * 0.5) / 4;
        spinners.push({ mesh: bigMesh, axis, speed });
      }

      // Small level cubes in a revolving ring
      const minRadius = (BIG_CUBE_SIZE + SMALL_CUBE_SIZE) / 2 + 0.3;
      const arcRadius = (n * RING_SPACING) / (2 * Math.PI);
      const radius = Math.max(minRadius, arcRadius);

      // Annulus (flat ring) passing through the small cubes
      if (n > 0) {
        const annulusGeo = new THREE.RingGeometry(radius - 0.04, radius + 0.04, 48);
        const annulus = new THREE.Mesh(annulusGeo, annulusMat);
        annulus.rotation.x = -Math.PI / 2;
        group.add(annulus);
      }

      // Sub-group that revolves around Y
      const ringGroup = new THREE.Group();
      group.add(ringGroup);
      orbiters.push({ group: ringGroup, speed: 0.15 + Math.random() * 0.1 });

      for (let i = 0; i < n; i++) {
        const angle = (2 * Math.PI * i) / n;
        const mesh = new THREE.Mesh(smallGeo, mat);
        mesh.position.set(
          Math.cos(angle) * radius,
          0,
          Math.sin(angle) * radius,
        );
        ringGroup.add(mesh);

        const axis = new THREE.Vector3(
          Math.random() - 0.5,
          Math.random() - 0.5,
          Math.random() - 0.5,
        ).normalize();
        const speed = (0.3 + Math.random() * 0.5) / 4;
        spinners.push({ mesh, axis, speed });
      }

      // --- Label ---
      const div = document.createElement('div');
      div.textContent = world.name;
      div.style.cssText = 'color:black;font:11px sans-serif;text-align:center;white-space:nowrap;background:rgba(255,255,255,0.75);border:1px solid black;border-radius:6px;padding:2px 6px;';
      const label = new CSS2DObject(div);
      label.position.set(0, 0, 0);
      group.add(label);
    });
  });

  // --- Dependency edges ---
  const lineMat = new LineMaterial({ color: 0x999999, linewidth: 2 });
  lineMat.resolution.set(width * window.devicePixelRatio, height * window.devicePixelRatio);
  for (const world of worlds) {
    const toGroup = worldToGroup.get(world.id);
    if (!toGroup) continue;
    for (const depId of world.dependsOn) {
      const fromGroup = worldToGroup.get(depId);
      if (!fromGroup) continue;
      const fp = fromGroup.position, tp = toGroup.position;
      const edgeGeo = new LineGeometry();
      edgeGeo.setPositions([fp.x, fp.y, fp.z, tp.x, tp.y, tp.z]);
      scene.add(new Line2(edgeGeo, lineMat));
    }
  }

  // --- Camera controls ---
  // Left-drag: orbit (rotate camera around a pivot point along the view direction)
  // Middle-drag: pan (translate camera sideways/up)
  // Scroll: zoom (move camera forward/backward along view direction)
  const ZOOM_SPEED = 1.5;
  const halfFovTan = Math.tan(THREE.MathUtils.degToRad(camera.fov / 2));

  camera.position.set(0, 20, 0);
  camera.up.set(0, 0, -1);
  camera.lookAt(0, 0, 0);
  const PIVOT_DISTANCE = 55.9;

  let isDragging = false;
  let dragButton = -1;
  let lastX = 0;
  let lastY = 0;

  // Reusable vectors
  const _right = new THREE.Vector3();
  const _forward = new THREE.Vector3();

  function onPointerDown(e: PointerEvent) {
    isDragging = true;
    dragButton = e.button;
    lastX = e.clientX;
    lastY = e.clientY;
    renderer.domElement.setPointerCapture(e.pointerId);
  }

  function onPointerMove(e: PointerEvent) {
    if (!isDragging) return;
    const dx = e.clientX - lastX;
    const dy = e.clientY - lastY;
    lastX = e.clientX;
    lastY = e.clientY;

    if (dragButton === 0 || dragButton === 1) {
      // Left or middle drag: pan — 1:1 pixel-to-world mapping
      const viewHeight = container.clientHeight;
      const dist = camera.position.y; // distance to y=0 ground plane
      const unitsPerPixel = (2 * dist * halfFovTan) / viewHeight;

      _right.setFromMatrixColumn(camera.matrixWorld, 0).normalize();
      const _camUp = new THREE.Vector3().setFromMatrixColumn(camera.matrixWorld, 1).normalize();

      camera.position.addScaledVector(_right, -dx * unitsPerPixel);
      camera.position.addScaledVector(_camUp, dy * unitsPerPixel);
    }
  }

  function onPointerUp(e: PointerEvent) {
    isDragging = false;
    dragButton = -1;
    renderer.domElement.releasePointerCapture(e.pointerId);
  }

  function onWheel(e: WheelEvent) {
    e.preventDefault();
    camera.getWorldDirection(_forward);
    const delta = e.deltaY > 0 ? -ZOOM_SPEED : ZOOM_SPEED;
    camera.position.addScaledVector(_forward, delta);
  }

  function onContextMenu(e: Event) { e.preventDefault(); }

  renderer.domElement.addEventListener('pointerdown', onPointerDown);
  renderer.domElement.addEventListener('pointermove', onPointerMove);
  renderer.domElement.addEventListener('pointerup', onPointerUp);
  renderer.domElement.addEventListener('wheel', onWheel, { passive: false });
  renderer.domElement.addEventListener('contextmenu', onContextMenu);

  // --- Animation loop ---
  const _spinQuat = new THREE.Quaternion();
  let animFrameId = 0;
  let lastTime = 0;
  function animate(t: number) {
    animFrameId = requestAnimationFrame(animate);
    const dt = (t - lastTime) / 1000;
    lastTime = t;
    if (dt > 0 && dt < 0.5) {
      for (const s of spinners) {
        _spinQuat.setFromAxisAngle(s.axis, s.speed * dt);
        s.mesh.quaternion.premultiply(_spinQuat);
      }
      for (const o of orbiters) {
        o.group.rotation.y += o.speed * dt;
      }
    }
    renderer.render(scene, camera);
    labelRenderer.render(scene, camera);
  }
  animFrameId = requestAnimationFrame(animate);

  // --- Resize ---
  const resizeObserver = new ResizeObserver(() => {
    const w = container.clientWidth;
    const h = container.clientHeight;
    if (w === 0 || h === 0) return;
    camera.aspect = w / h;
    camera.updateProjectionMatrix();
    renderer.setSize(w, h);
    labelRenderer.setSize(w, h);
    lineMat.resolution.set(w * window.devicePixelRatio, h * window.devicePixelRatio);
  });
  resizeObserver.observe(container);

  return {
    dispose() {
      cancelAnimationFrame(animFrameId);
      resizeObserver.disconnect();
      renderer.domElement.removeEventListener('pointerdown', onPointerDown);
      renderer.domElement.removeEventListener('pointermove', onPointerMove);
      renderer.domElement.removeEventListener('pointerup', onPointerUp);
      renderer.domElement.removeEventListener('wheel', onWheel);
      renderer.domElement.removeEventListener('contextmenu', onContextMenu);
      renderer.dispose();
      bigGeo.dispose();
      smallGeo.dispose();
      annulusMat.dispose();
      lineMat.dispose();
      scene.traverse(obj => {
        if (obj instanceof THREE.Mesh) {
          if (obj.material instanceof THREE.Material) obj.material.dispose();
        }
        if (obj instanceof Line2) {
          obj.geometry.dispose();
        }
      });
      if (renderer.domElement.parentElement) {
        renderer.domElement.parentElement.removeChild(renderer.domElement);
      }
      if (labelRenderer.domElement.parentElement) {
        labelRenderer.domElement.parentElement.removeChild(labelRenderer.domElement);
      }
    },
  };
}
