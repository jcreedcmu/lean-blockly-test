import * as THREE from 'three';
import { EffectComposer } from 'three/examples/jsm/postprocessing/EffectComposer.js';
import { RenderPass } from 'three/examples/jsm/postprocessing/RenderPass.js';
import { SAOPass } from 'three/examples/jsm/postprocessing/SAOPass.js';
import { ShaderPass } from 'three/examples/jsm/postprocessing/ShaderPass.js';
import { FXAAShader } from 'three/examples/jsm/shaders/FXAAShader.js';
import { TrackballControls } from 'three/examples/jsm/controls/TrackballControls.js';
import type { World } from './gameData';
import { getWorldRows } from './gameData';

// Color palette for world cubes
const PALETTE = [
  0xdd3333, 0x33bb33, 0x3333dd,
  0xddaa33, 0xaa33dd, 0x33dddd,
  0xdd6633, 0x66dd33, 0x3366dd,
];

export type SceneCallbacks = {
  onHover: (world: World | null, screenX: number, screenY: number) => void;
  onSelect: (worldId: string) => void;
};

export function init(
  container: HTMLElement,
  worlds: World[],
  callbacks: SceneCallbacks,
): { dispose: () => void } {
  // --- Scene, camera, renderer ---
  const scene = new THREE.Scene();
  scene.background = new THREE.Color(0x000000);

  const width = container.clientWidth;
  const height = container.clientHeight;

  const camera = new THREE.PerspectiveCamera(50, width / height, 0.1, 100);
  camera.position.set(5, 5, 5);
  camera.lookAt(0, 0, 0);

  const renderer = new THREE.WebGLRenderer({ antialias: true });
  renderer.setSize(width, height);
  renderer.setPixelRatio(window.devicePixelRatio);
  container.appendChild(renderer.domElement);

  // --- Lighting ---
  scene.add(new THREE.AmbientLight(0xffffff, 1.0));
  const dirLight = new THREE.DirectionalLight(0xffffff, 2.0);
  dirLight.position.set(-5, 8, 1);
  camera.add(dirLight);
  scene.add(camera);

  // --- Build world cubes + lookup ---
  const rows = getWorldRows(worlds);
  const meshToWorld = new Map<THREE.Mesh, World>();
  const worldToMesh = new Map<string, THREE.Mesh>();

  const SPACING_X = 2.5;
  const SPACING_Z = 2.5;

  rows.forEach((row, ri) => {
    const rowWidth = (row.length - 1) * SPACING_X;
    row.forEach((world, ci) => {
      const colorIndex = worlds.indexOf(world) % PALETTE.length;
      const mat = new THREE.MeshStandardMaterial({ color: PALETTE[colorIndex] });
      const geo = new THREE.BoxGeometry(1, 1, 1);
      const mesh = new THREE.Mesh(geo, mat);
      mesh.position.set(
        ci * SPACING_X - rowWidth / 2,
        0,
        ri * SPACING_Z,
      );
      scene.add(mesh);
      meshToWorld.set(mesh, world);
      worldToMesh.set(world.id, mesh);
    });
  });

  // --- Dependency edges ---
  const lineMat = new THREE.LineBasicMaterial({ color: 0x555555 });
  for (const world of worlds) {
    const toMesh = worldToMesh.get(world.id);
    if (!toMesh) continue;
    for (const depId of world.dependsOn) {
      const fromMesh = worldToMesh.get(depId);
      if (!fromMesh) continue;
      const points = [fromMesh.position.clone(), toMesh.position.clone()];
      const geo = new THREE.BufferGeometry().setFromPoints(points);
      scene.add(new THREE.Line(geo, lineMat));
    }
  }

  // --- Mask render target (for outline shader) ---
  const pixelW = width * window.devicePixelRatio;
  const pixelH = height * window.devicePixelRatio;
  const maskTarget = new THREE.WebGLRenderTarget(pixelW, pixelH);
  const maskMat = new THREE.MeshBasicMaterial({ color: 0xffffff });
  const maskBg = new THREE.Color(0x000000);

  // --- Outline shader ---
  const OutlineShader = {
    uniforms: {
      tDiffuse: { value: null as THREE.Texture | null },
      tMask: { value: maskTarget.texture },
      outlineColor: { value: new THREE.Color(0xffff00) },
      resolution: { value: new THREE.Vector2(pixelW, pixelH) },
      innerRadius: { value: 4.0 },
      outerRadius: { value: 8.0 },
    },
    vertexShader: `
      varying vec2 vUv;
      void main() {
        vUv = uv;
        gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
      }
    `,
    fragmentShader: `
      uniform sampler2D tDiffuse;
      uniform sampler2D tMask;
      uniform vec3 outlineColor;
      uniform vec2 resolution;
      uniform float innerRadius;
      uniform float outerRadius;
      varying vec2 vUv;

      void main() {
        vec4 sceneCol = texture2D(tDiffuse, vUv);
        float dInner = 0.0;
        float dOuter = 0.0;
        for (float a = 0.0; a < 6.2832; a += 0.3927) {
          vec2 dir = vec2(cos(a), sin(a));
          for (float r = 1.0; r <= 30.0; r += 1.0) {
            float s = texture2D(tMask, vUv + dir * r / resolution).r;
            dInner = max(dInner, s * step(r, innerRadius));
            dOuter = max(dOuter, s * step(r, outerRadius));
          }
        }
        float outline = dOuter * (1.0 - dInner);
        gl_FragColor = vec4(mix(sceneCol.rgb, outlineColor, outline), 1.0);
      }
    `,
  };

  // --- Post-processing ---
  const composer = new EffectComposer(renderer);
  composer.addPass(new RenderPass(scene, camera));

  const sao = new SAOPass(scene, camera);
  sao.params.saoIntensity = 0.02;
  sao.params.saoScale = 3;
  sao.params.saoKernelRadius = 40;
  sao.params.saoBias = 0.5;
  composer.addPass(sao);

  const outlinePass = new ShaderPass(OutlineShader);
  outlinePass.uniforms.tMask.value = maskTarget.texture;
  composer.addPass(outlinePass);

  const fxaa = new ShaderPass(FXAAShader);
  fxaa.uniforms['resolution'].value.set(
    1 / pixelW,
    1 / pixelH,
  );
  composer.addPass(fxaa);

  // --- Controls ---
  const controls = new TrackballControls(camera, renderer.domElement);
  controls.rotateSpeed = 5.0;
  controls.noRotate = false;
  controls.noPan = true;
  controls.mouseButtons.LEFT = THREE.MOUSE.RIGHT as unknown as number; // rotate on right-click
  controls.mouseButtons.RIGHT = null as unknown as number;
  controls.mouseButtons.MIDDLE = THREE.MOUSE.MIDDLE as unknown as number;

  // --- Raycaster / hover state ---
  const raycaster = new THREE.Raycaster();
  const mouse = new THREE.Vector2();
  let hoveredMesh: THREE.Mesh | null = null;
  const allMeshes = Array.from(meshToWorld.keys());

  function onMouseMove(e: MouseEvent) {
    const rect = container.getBoundingClientRect();
    mouse.x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
    mouse.y = -((e.clientY - rect.top) / rect.height) * 2 + 1;

    updateHover();

    if (hoveredMesh) {
      callbacks.onHover(meshToWorld.get(hoveredMesh)!, e.clientX, e.clientY);
    } else {
      callbacks.onHover(null, 0, 0);
    }
  }

  function updateHover() {
    raycaster.setFromCamera(mouse, camera);
    const hits = raycaster.intersectObjects(allMeshes, false);
    const hit = hits.length > 0 ? (hits[0].object as THREE.Mesh) : null;
    if (hit !== hoveredMesh) {
      hoveredMesh = hit;
    }
  }

  container.addEventListener('mousemove', onMouseMove);

  // --- Click with drag guard ---
  let mouseDownPos = { x: 0, y: 0 };

  function onMouseDown(e: MouseEvent) {
    mouseDownPos = { x: e.clientX, y: e.clientY };
  }

  function onClick(e: MouseEvent) {
    const dx = e.clientX - mouseDownPos.x;
    const dy = e.clientY - mouseDownPos.y;
    if (Math.sqrt(dx * dx + dy * dy) > 5) return; // was a drag

    if (hoveredMesh) {
      const world = meshToWorld.get(hoveredMesh);
      if (world) {
        bounces.push({
          mesh: hoveredMesh,
          startTime: performance.now(),
          baseScale: hoveredMesh.scale.x,
        });
        callbacks.onSelect(world.id);
      }
    }
  }

  container.addEventListener('mousedown', onMouseDown);
  container.addEventListener('click', onClick);

  // --- Bounce animation ---
  type Bounce = { mesh: THREE.Mesh; startTime: number; baseScale: number };
  const bounces: Bounce[] = [];

  function updateBounces(t: number) {
    for (let i = bounces.length - 1; i >= 0; i--) {
      const b = bounces[i];
      const elapsed = (t - b.startTime) / 1000;
      const duration = 0.5;
      if (elapsed >= duration) {
        b.mesh.scale.setScalar(b.baseScale);
        bounces.splice(i, 1);
      } else {
        const p = elapsed / duration;
        const bump = Math.sin(p * Math.PI) * Math.exp(-p * 3);
        b.mesh.scale.setScalar(b.baseScale * (1 + bump * 0.8));
      }
    }
  }

  // --- Mask render ---
  function renderMask() {
    const bg = scene.background;
    scene.background = maskBg;
    scene.overrideMaterial = maskMat;

    const vis: boolean[] = [];
    scene.traverse(obj => vis.push(obj.visible));
    scene.traverse(obj => { obj.visible = false; });

    if (hoveredMesh) {
      hoveredMesh.visible = true;
      let p: THREE.Object3D | null = hoveredMesh.parent;
      while (p) { p.visible = true; p = p.parent; }
    }

    renderer.setRenderTarget(maskTarget);
    renderer.clear();
    renderer.render(scene, camera);
    renderer.setRenderTarget(null);

    let i = 0;
    scene.traverse(obj => { obj.visible = vis[i++]; });
    scene.overrideMaterial = null;
    scene.background = bg;
  }

  // --- Context menu suppress ---
  function onContextMenu(e: Event) { e.preventDefault(); }
  renderer.domElement.addEventListener('contextmenu', onContextMenu);

  // --- Animation loop ---
  let animFrameId = 0;

  function animate(t: number) {
    animFrameId = requestAnimationFrame(animate);
    const s = t * 0.001;

    // Gentle Y rotation on cubes
    for (const mesh of allMeshes) {
      mesh.rotation.y = s * 0.3;
    }

    updateBounces(t);
    renderMask();
    controls.update();
    composer.render();
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
    composer.setSize(w, h);

    const pw = w * window.devicePixelRatio;
    const ph = h * window.devicePixelRatio;
    maskTarget.setSize(pw, ph);
    outlinePass.uniforms.resolution.value.set(pw, ph);
    fxaa.uniforms['resolution'].value.set(1 / pw, 1 / ph);
  });
  resizeObserver.observe(container);

  // --- Dispose ---
  return {
    dispose() {
      cancelAnimationFrame(animFrameId);
      resizeObserver.disconnect();
      container.removeEventListener('mousemove', onMouseMove);
      container.removeEventListener('mousedown', onMouseDown);
      container.removeEventListener('click', onClick);
      renderer.domElement.removeEventListener('contextmenu', onContextMenu);
      controls.dispose();
      composer.dispose();
      renderer.dispose();
      maskTarget.dispose();
      maskMat.dispose();
      lineMat.dispose();

      scene.traverse(obj => {
        if (obj instanceof THREE.Mesh) {
          obj.geometry.dispose();
          if (Array.isArray(obj.material)) {
            obj.material.forEach(m => m.dispose());
          } else {
            obj.material.dispose();
          }
        }
        if (obj instanceof THREE.Line) {
          obj.geometry.dispose();
        }
      });

      if (renderer.domElement.parentElement) {
        renderer.domElement.parentElement.removeChild(renderer.domElement);
      }
    },
  };
}
