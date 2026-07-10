/* Climate Reality Leaders — WebGL map engine (Three.js).
 * Replaces map.js. Same public surface: window.__mapApi.
 * Renders arcs with tapered glow, instanced dots, bloom post-processing.
 */
(function () {
  "use strict";

  // ---------- Config ----------
  const CONFIG = {
    yearMs: 6000,
    pulseMs: 900,
    arcDrawMs: 900,
    arcHoldMs: 300,
    arcFadeMs: 600,
    originRadiusBase: 2.4,
    originRadiusK: 0.42,
    destRadiusBase: 1.8,
    destRadiusK: 0.52,
    arcSamples: 48,
    arcWidth: 0.6,
    particlesPerArc: 0,
    bloomStrength: 0.7,
    bloomRadius: 0.4,
  };
  const ARC_LIFE = CONFIG.arcDrawMs + CONFIG.arcHoldMs + CONFIG.arcFadeMs;

  // ---------- State ----------
  let events = [];
  let YEAR0, YEAR1, TOTAL_YEARS, TOTAL_MS;

  let renderer, scene, camera, composer;
  let landGroup, arcGroup, dotGroup, particleGroup;
  let width, height, pixelRatio;
  let projection, pathGen;
  let countries = null;

  const playState = {
    playing: true,
    speed: 1,
    currentTimeMs: 0,
    lastFrameTs: 0,
    finishedExtraMs: 0,
  };

  const destState = new Map();
  const originState = new Map();
  const countrySet = new Set();
  let liveArcs = [];
  let processedThrough = -1;
  let stats = { leaders: 0, countries: 0 };

  // Tweak-driven
  let dotScale = 1.0;
  let showLabels = true;
  let arcStyle = "straight";   // straight lines (great-circle was the curved default)
  let theme = "light";         // light cream backdrop is the default look
  let colorOverrides = { origin: "", dest: "", arc: "" };

  // Three.js objects pools
  let originDots = new Map();   // key -> mesh
  let destDots = new Map();     // key -> mesh
  let arcMeshes = [];           // {id, mesh, glowMesh, born, progress}
  let particleSystems = [];     // {id, points, born, path}
  let pulseMeshes = [];         // {mesh, born, origin}
  let highlightRings = [];      // active geographic highlight rings

  // Org layer — static branch/chapter/hub markers from data/org.json.
  // Each marker reveals at its founding year along the same timeline.
  let orgData = null;
  let orgGroup = null;
  let orgMarkers = [];          // {mesh, founded, shownAt}
  let orgVisible = true;
  const ORG_SIZES = { branchInner: 11, branchOuter: 16, chapter: 5, hub: 5 };

  // Annotations — persistent markers pinned to the timeline
  // highlight: [lon, lat] to briefly brighten that region when annotation fires
  const ANNOTATIONS = [
    { ms: null, year: 2006.5, text: "It started with 50 people in a single room in Nashville.", revealed: false, highlight: [-86.78, 36.16] },
    { ms: null, year: 2010.5, text: "In four years, trainings have spread to five continents.", revealed: false, highlight: null },
    { ms: null, year: 2014.0, text: "The 10,000th Leader is trained.", revealed: false, highlight: null },
    { ms: null, year: 2014.5, text: "Training reaches Sub-Saharan Africa for the first time.", revealed: false, highlight: [28.05, -26.2] },
    { ms: null, year: 2020.5, text: "The pandemic shifts everything online and virtual trainings surge.", revealed: false, highlight: null },
    { ms: null, year: 2025.0, text: "The REALITY Tour© kicks off across Rio de Janeiro, Nairobi, Paris, and Ulaanbaatar.", revealed: false, highlight: null },
    { ms: null, year: 2025.8, text: "The movement now spans 54,558 Leaders across 195 countries.", revealed: false, highlight: null },
  ];
  let annotationContainer = null;
  let highlightRing = null;  // geographic highlight mesh

  // ---------- Colors ----------
  function getColors() {
    const dark = theme === "dark";
    return {
      // Match CSS variables from index.html
      bg: dark ? 0x10502F : 0xF4F5EC,
      land: dark ? 0x457428 : 0xD4DF9B,
      landStroke: dark ? 0x56892F : 0xB5C47A,
      graticule: dark ? 0x1A5E35 : 0xE0E3D8,
      origin: colorOverrides.origin ? parseInt(colorOverrides.origin.replace("#",""), 16) : (dark ? 0x8DC63F : 0xC0D110),
      virtual: dark ? 0xFFC500 : 0xE5A800,
      dest: colorOverrides.dest ? parseInt(colorOverrides.dest.replace("#",""), 16) : (dark ? 0xD4DF9B : 0x457428),
      arc: colorOverrides.arc ? parseInt(colorOverrides.arc.replace("#",""), 16) : (dark ? 0xC0D110 : 0x457428),
      text: dark ? 0xE6E6E6 : 0x10502F,
      // Org layer: green ring anchors a branch region; gold diamonds mark local chapters/hubs.
      orgBranch: dark ? 0xC0D110 : 0x457428,
      orgLocal:  dark ? 0xFFC500 : 0xE5A800,
    };
  }

  // ---------- Helpers ----------
  // Normalized √ scaling: 15 leaders -> r 3, the highest real count -> r 35.
  // The generic "Virtual" total is an outlier (~16k) — anchoring the scale to
  // it crushes the mid-range, so cap the scale at the highest non-virtual count
  // (HI) and give anything above it a fixed, slightly-larger outlier size.
  const SQ_LO = Math.sqrt(15), HI = 4502, SQ_HI = Math.sqrt(HI);
  function dotRadius(cum) {
    if (cum > HI) return 40 * dotScale;           // outsized generic "Virtual"
    const n = Math.max(0, Math.min(1, (Math.sqrt(cum) - SQ_LO) / (SQ_HI - SQ_LO)));
    return (3 + n * (35 - 3)) * dotScale;
  }
  function destRadius(cum)   { return dotRadius(cum); }
  function originRadius(cum) { return dotRadius(cum); }

  function eventFireMs(ev) {
    const d = new Date(ev.date);
    const y = d.getUTCFullYear() + (d.getUTCMonth() / 12) + (d.getUTCDate() / 365);
    return (y - YEAR0) * CONFIG.yearMs;
  }

  function yearAt(ms) {
    return YEAR0 + ms / CONFIG.yearMs;
  }

  function isVirtualEvent(ev) {
    return /virtual/i.test(ev.city);
  }

  const MONTHS = ["January","February","March","April","May","June",
                  "July","August","September","October","November","December"];
  function monthLabelAt(ms) {
    const yFloat = yearAt(ms);
    const yInt = Math.floor(yFloat);
    const monthIdx = Math.min(11, Math.max(0, Math.floor((yFloat - yInt) * 12)));
    return MONTHS[monthIdx];
  }

  // Project [lon,lat] -> [x,y] in screen coords (centered on 0,0 for Three.js)
  function project(lonLat) {
    const p = projection(lonLat);
    if (!p) return null;
    return [p[0] - width / 2, -(p[1] - height / 2)];
  }

  // ---------- Three.js Setup ----------
  // Mobile detection helper
  const isMobile = () => window.innerWidth <= 768 || (window.innerHeight <= 500 && window.innerWidth <= 1024);

  // Build the Natural Earth projection sized to the current viewport. Used both
  // at init and on every resize so the map, dots, and coastlines always share
  // exactly one projection at any window size.
  function makeProjection() {
    const isLandscape = window.innerHeight <= 500 && window.innerWidth > window.innerHeight;
    let scaleFactor;
    if (isLandscape)      scaleFactor = height / 2.8;
    else if (isMobile())  scaleFactor = width / 4.8;
    else                  scaleFactor = width / 6.2;
    const yOffset = isMobile() ? height * 0.02 : 10;
    return d3.geoNaturalEarth1()
      .scale(scaleFactor)
      .translate([width / 2, height / 2 + yOffset]);
  }

  function initThree() {
    const container = document.getElementById("app");
    width = container.clientWidth;
    height = container.clientHeight;
    pixelRatio = window.devicePixelRatio || 1;

    // Scale dots down on mobile so they don't overwhelm the small screen
    if (isMobile()) {
      dotScale = 0.6;
      CONFIG.arcWidth = 0.7;
    }

    // Renderer
    renderer = new THREE.WebGLRenderer({ antialias: true, alpha: false });
    renderer.setSize(width, height);
    renderer.setPixelRatio(pixelRatio);
    renderer.setClearColor(getColors().bg);

    // Insert canvas before the SVG (which we'll hide)
    const svgEl = document.getElementById("map");
    if (svgEl) svgEl.style.display = "none";
    container.insertBefore(renderer.domElement, container.firstChild);
    renderer.domElement.style.position = "absolute";
    renderer.domElement.style.top = "0";
    renderer.domElement.style.left = "0";

    // Camera — orthographic, maps screen pixels
    camera = new THREE.OrthographicCamera(
      -width / 2, width / 2,
      height / 2, -height / 2,
      0.1, 1000
    );
    camera.position.z = 100;

    scene = new THREE.Scene();

    // Layer groups (z-ordering via position.z)
    landGroup = new THREE.Group(); landGroup.position.z = 0;
    arcGroup = new THREE.Group(); arcGroup.position.z = 2;
    dotGroup = new THREE.Group(); dotGroup.position.z = 3;
    particleGroup = new THREE.Group(); particleGroup.position.z = 4;
    orgGroup = new THREE.Group(); orgGroup.position.z = 4.5;

    scene.add(landGroup);
    scene.add(arcGroup);
    scene.add(dotGroup);
    scene.add(particleGroup);
    scene.add(orgGroup);

    // Bloom via simple additive pass (we'll do a manual approach)
    setupBloom();

    // Projection (same sizing logic as onResize, via makeProjection)
    projection = makeProjection();
    pathGen = d3.geoPath(projection);

    // Milestone text element — appears above the year display
    milestoneEl = document.getElementById("milestone-text");

    // Resize
    window.addEventListener("resize", onResize);
  }

  // Simple bloom: render arcs to a separate target, blur, composite
  let bloomTarget, bloomScene, bloomCamera, bloomQuad;
  function setupBloom() {
    // We'll use a simpler approach: just render arcs with emissive materials
    // and add a glow sprite behind each arc. True multi-pass bloom requires
    // EffectComposer which isn't in core Three.js CDN. Instead we fake it
    // with wider, semi-transparent duplicate geometry.
  }

  function onResize() {
    const container = document.getElementById("app");
    width = container.clientWidth;
    height = container.clientHeight;

    renderer.setSize(width, height);
    camera.left = -width / 2;
    camera.right = width / 2;
    camera.top = height / 2;
    camera.bottom = -height / 2;
    camera.updateProjectionMatrix();

    // Rebuild the projection AND rebind the path generator to it. Rebinding is
    // essential: without it the land/graticule keep drawing at the old size
    // while the dots reproject to the new size, so they drift apart on resize.
    projection = makeProjection();
    pathGen = d3.geoPath(projection);

    // Adjust dot scale on orientation change
    dotScale = isMobile() ? 0.6 : 1.0;

    rebuildStaticLayers();
    hardResync(playState.currentTimeMs);
  }

  // ---------- Static Layers ----------
  function rebuildStaticLayers() {
    // Clear
    while (landGroup.children.length) landGroup.remove(landGroup.children[0]);

    const colors = getColors();
    renderer.setClearColor(colors.bg);

    // Graticule
    const grat = d3.geoGraticule().step([20, 20])();
    const gratPath = pathGen(grat);
    if (gratPath) {
      const gratShape = pathToShape(gratPath);
      if (gratShape) {
        const gratMat = new THREE.LineBasicMaterial({ color: colors.graticule, transparent: true, opacity: 0.4 });
        gratShape.forEach(pts => {
          const geo = new THREE.BufferGeometry().setFromPoints(pts);
          landGroup.add(new THREE.Line(geo, gratMat));
        });
      }
    }

    // Land polygons
    if (countries) {
      countries.forEach(feature => {
        const p = pathGen(feature);
        if (!p) return;
        const lines = pathToShape(p);
        if (!lines) return;
        const mat = new THREE.LineBasicMaterial({ color: colors.landStroke, transparent: true, opacity: 0.8 });
        lines.forEach(pts => {
          if (pts.length < 2) return;
          const geo = new THREE.BufferGeometry().setFromPoints(pts);
          landGroup.add(new THREE.Line(geo, mat));
        });
      });

      // Land fill intentionally omitted — show country borders (strokes) only,
      // no shading fill.
    }

    // Org markers are projected, so rebuild them whenever projection/theme changes.
    buildOrgLayer();
  }

  // ---------- Org layer (2D) ----------
  // Branch = ring + solid core; chapter/hub = matte solid bead. No additive
  // glow here: the flat map's default light/cream background blows out under
  // additive blending. Crisp matte shapes read cleanly on both themes.
  const ORG_GOLD = { branch: 0xFFC500, chapter: 0xFFC500, hub: 0xFFC500 };

  function makeOrgMesh(kind, color, opacity) {
    const group = new THREE.Group();

    if (kind === "branch") {
      // Branch = solid gold diamond (a rotated 4-gon). The old ring+core read
      // as a bullseye / target. Diamond = "regional anchor", clearly distinct
      // from the round chapter/hub beads.
      const diamond = new THREE.Mesh(
        new THREE.CircleGeometry(ORG_SIZES.branchOuter * dotScale, 4),
        new THREE.MeshBasicMaterial({ color, transparent: true, opacity: 0.97, side: THREE.DoubleSide, depthTest: false })
      );
      diamond.rotation.z = Math.PI / 4;
      diamond.renderOrder = 21;
      group.add(diamond);
    } else {
      // Chapter / hub = matte solid bead, quiet and readable.
      const bead = new THREE.Mesh(
        new THREE.CircleGeometry(ORG_SIZES.hub * dotScale, 20),
        new THREE.MeshBasicMaterial({ color, transparent: true, opacity: Math.max(0.7, opacity), side: THREE.DoubleSide, depthTest: false })
      );
      bead.renderOrder = 20;
      group.add(bead);
    }
    return group;
  }

  // "YYYY-MM" -> fractional year (e.g. "2009-12" -> 2009.92).
  function yearFromYM(ym) {
    if (!ym) return null;
    const [y, m] = ym.split("-").map(Number);
    return y + ((m || 1) - 1) / 12;
  }

  function addOrgMarker(kind, lon, lat, color, opacity, founded, revealAfter) {
    const p = project([lon, lat]);
    if (!p) return;
    const mesh = makeOrgMesh(kind, color, opacity);
    mesh.position.set(p[0], p[1], 0);
    mesh.scale.set(0, 0, 1);
    mesh.visible = false;
    orgGroup.add(mesh);
    // Branches carry reveal_after = the month their launching training was held,
    // so the training always appears before the branch marker. Chapters/hubs
    // (no reveal_after) reveal mid-founding-year.
    const ra = yearFromYM(revealAfter);
    const revealYear = ra != null ? ra : founded + 0.5;
    orgMarkers.push({ mesh, founded, revealYear, shownAt: null });
  }

  function buildOrgLayer() {
    if (!orgGroup) return;
    while (orgGroup.children.length) {
      const c = orgGroup.children[0];
      orgGroup.remove(c);
      c.traverse(o => {
        if (o.geometry) o.geometry.dispose();
        if (o.material) o.material.dispose();
      });
    }
    orgMarkers = [];
    if (!orgData) return;
    (orgData.branches || []).forEach(b =>
      addOrgMarker("branch", b.lon, b.lat, ORG_GOLD.branch, 0.5, b.founded, b.reveal_after));
    (orgData.chapters || []).forEach(c =>
      addOrgMarker("chapter", c.lon, c.lat, ORG_GOLD.chapter, c.approx ? 0.5 : 0.85, c.founded));
    (orgData.hubs || []).forEach(h =>
      addOrgMarker("hub", h.lon, h.lat, ORG_GOLD.hub, 0.9, h.founded));
  }

  // Parse SVG path d to arrays of THREE.Vector2 points (for lines)
  function pathToShape(d) {
    if (!d) return null;
    const segments = [];
    let current = [];
    const commands = d.match(/[ML][^ML]*/g);
    if (!commands) return null;

    commands.forEach(cmd => {
      const type = cmd[0];
      const coords = cmd.slice(1).trim().split(/[\s,]+/).map(Number);
      for (let i = 0; i < coords.length; i += 2) {
        const x = coords[i] - width / 2;
        const y = -(coords[i + 1] - height / 2);
        if (type === "M") {
          if (current.length > 1) segments.push(current);
          current = [new THREE.Vector2(x, y)];
        } else {
          current.push(new THREE.Vector2(x, y));
        }
      }
    });
    if (current.length > 1) segments.push(current);
    return segments.length ? segments : null;
  }

  // Parse SVG path to THREE.Shape (for filled polygons)
  function pathToThreeShapes(d) {
    const shapes = [];
    const parts = d.split(/(?=[M])/);
    parts.forEach(part => {
      const cmds = part.match(/[ML][^ML]*/g);
      if (!cmds || cmds.length < 3) return;
      const shape = new THREE.Shape();
      let first = true;
      cmds.forEach(cmd => {
        const type = cmd[0];
        const coords = cmd.slice(1).trim().split(/[\s,]+/).map(Number);
        for (let i = 0; i < coords.length; i += 2) {
          const x = coords[i] - width / 2;
          const y = -(coords[i + 1] - height / 2);
          if (first) { shape.moveTo(x, y); first = false; }
          else shape.lineTo(x, y);
        }
      });
      shapes.push(shape);
    });
    return shapes;
  }

  // ---------- Arc Geometry ----------
  function createArcGeometry(p1, p2) {
    // Outward: training -> leaders' home.
    // Generate points along the path
    const pts = [];
    if (arcStyle === "great-circle") {
      const interp = d3.geoInterpolate(p1, p2);
      const lonLats = [];
      for (let i = 0; i <= CONFIG.arcSamples; i++) {
        lonLats.push(interp(i / CONFIG.arcSamples));
      }
      // Split at antimeridian crossings to avoid horizontal wrap stripes
      const segments = [[]];
      for (let i = 0; i < lonLats.length; i++) {
        if (i > 0 && Math.abs(lonLats[i][0] - lonLats[i - 1][0]) > 180) {
          segments.push([]);
        }
        segments[segments.length - 1].push(lonLats[i]);
      }
      // Keep the longest segment (closest to the visible path)
      const longest = segments.reduce((a, b) => a.length > b.length ? a : b);
      longest.forEach(ll => {
        const xy = project(ll);
        if (xy) pts.push(xy);
      });
    } else {
      const a = project(p1);
      const b = project(p2);
      if (a && b) {
        for (let i = 0; i <= CONFIG.arcSamples; i++) {
          const t = i / CONFIG.arcSamples;
          pts.push([a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t]);
        }
      }
    }
    if (pts.length < 2) return null;

    // Build a tapered ribbon
    const positions = [];
    const alphas = [];
    const progresses = [];

    for (let i = 0; i < pts.length; i++) {
      const t = i / (pts.length - 1);
      // Connection style: a quiet, near-uniform thin line.
      const taper = CONFIG.arcWidth * 0.5 * dotScale;

      // Normal direction (perpendicular to path)
      let nx, ny;
      if (i === 0) {
        nx = -(pts[1][1] - pts[0][1]);
        ny = pts[1][0] - pts[0][0];
      } else if (i === pts.length - 1) {
        nx = -(pts[i][1] - pts[i-1][1]);
        ny = pts[i][0] - pts[i-1][0];
      } else {
        nx = -(pts[i+1][1] - pts[i-1][1]);
        ny = pts[i+1][0] - pts[i-1][0];
      }
      const len = Math.sqrt(nx * nx + ny * ny) || 1;
      nx /= len; ny /= len;

      // Two vertices per point (ribbon)
      positions.push(pts[i][0] + nx * taper, pts[i][1] + ny * taper, 0);
      positions.push(pts[i][0] - nx * taper, pts[i][1] - ny * taper, 0);
      // Quiet uniform line.
      alphas.push(0.9);
      alphas.push(0.9);
      progresses.push(t);
      progresses.push(t);
    }

    // Triangle strip indices
    const indices = [];
    for (let i = 0; i < pts.length - 1; i++) {
      const a = i * 2, b = i * 2 + 1, c = (i + 1) * 2, d_ = (i + 1) * 2 + 1;
      indices.push(a, b, c);
      indices.push(b, d_, c);
    }

    const geo = new THREE.BufferGeometry();
    geo.setAttribute("position", new THREE.Float32BufferAttribute(positions, 3));
    geo.setAttribute("alpha", new THREE.Float32BufferAttribute(alphas, 1));
    geo.setAttribute("progress", new THREE.Float32BufferAttribute(progresses, 1));
    geo.setIndex(indices);
    return { geo, path: pts };
  }

  // Arc shader material
  function createArcMaterial(color, opacity) {
    return new THREE.ShaderMaterial({
      transparent: true,
      depthWrite: false,
      uniforms: {
        uColor: { value: new THREE.Color(color) },
        uOpacity: { value: opacity },
        uDrawProgress: { value: 0.0 },
      },
      vertexShader: `
        attribute float alpha;
        attribute float progress;
        varying float vAlpha;
        varying float vProgress;
        void main() {
          vAlpha = alpha;
          vProgress = progress;
          gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
        }
      `,
      fragmentShader: `
        uniform vec3 uColor;
        uniform float uOpacity;
        uniform float uDrawProgress;
        varying float vAlpha;
        varying float vProgress;
        void main() {
          if (vProgress > uDrawProgress) discard;
          float a = vAlpha * uOpacity * smoothstep(uDrawProgress - 0.02, uDrawProgress, vProgress) * 0.5 + vAlpha * uOpacity * 0.5;
          gl_FragColor = vec4(uColor, a);
        }
      `,
    });
  }

  // Glow version (wider, more transparent)
  function createGlowMaterial(color) {
    return new THREE.ShaderMaterial({
      transparent: true,
      depthWrite: false,
      uniforms: {
        uColor: { value: new THREE.Color(color) },
        uOpacity: { value: 0.3 },
        uDrawProgress: { value: 0.0 },
      },
      vertexShader: `
        attribute float alpha;
        attribute float progress;
        varying float vAlpha;
        varying float vProgress;
        void main() {
          vAlpha = alpha;
          vProgress = progress;
          gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 1.0);
        }
      `,
      fragmentShader: `
        uniform vec3 uColor;
        uniform float uOpacity;
        uniform float uDrawProgress;
        varying float vAlpha;
        varying float vProgress;
        void main() {
          if (vProgress > uDrawProgress) discard;
          float a = vAlpha * uOpacity;
          gl_FragColor = vec4(uColor, a);
        }
      `,
    });
  }

  // ---------- Dot creation ----------
  const dotGeoCache = {};
  function getDotGeo(radius) {
    const key = Math.round(radius * 10);
    if (!dotGeoCache[key]) {
      dotGeoCache[key] = new THREE.CircleGeometry(radius, 24);
    }
    return dotGeoCache[key];
  }

  function createDot(x, y, radius, color, opacity) {
    const geo = new THREE.CircleGeometry(radius, 24);
    const mat = new THREE.MeshBasicMaterial({ color, transparent: true, opacity });
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.set(x, y, 0);
    // Entrance animation: start at scale 0, animate to 1 with elastic overshoot
    mesh.scale.set(0, 0, 1);
    mesh.userData.targetScale = 1;
    mesh.userData.birthTime = playState.currentTimeMs;
    mesh.userData.animating = true;
    return mesh;
  }

  // Elastic ease out: overshoots then settles
  function elasticOut(t) {
    if (t === 0 || t === 1) return t;
    return Math.pow(2, -10 * t) * Math.sin((t - 0.075) * (2 * Math.PI) / 0.3) + 1;
  }

  // Geographic highlight ring for annotations
  function createHighlightRing(lonLat) {
    const p = project(lonLat);
    if (!p) return null;
    const geo = new THREE.RingGeometry(20, 55, 48);
    const colors = getColors();
    const mat = new THREE.MeshBasicMaterial({
      color: colors.origin,
      transparent: true,
      opacity: 0,
      side: THREE.DoubleSide,
    });
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.set(p[0], p[1], 6);
    mesh.userData.birthTime = performance.now();
    mesh.userData.duration = 3000; // 3s fade cycle
    scene.add(mesh);
    return mesh;
  }

  // ---------- Particle system ----------
  function createParticles(path, color) {
    const count = CONFIG.particlesPerArc;
    const geo = new THREE.BufferGeometry();
    const positions = new Float32Array(count * 3);
    const sizes = new Float32Array(count);

    for (let i = 0; i < count; i++) {
      positions[i * 3] = path[0][0];
      positions[i * 3 + 1] = path[0][1];
      positions[i * 3 + 2] = 5;
      sizes[i] = 2.5;
    }

    geo.setAttribute("position", new THREE.Float32BufferAttribute(positions, 3));
    geo.setAttribute("size", new THREE.Float32BufferAttribute(sizes, 1));

    const mat = new THREE.PointsMaterial({
      color: color,
      size: 3 * dotScale,
      transparent: true,
      opacity: 0.9,
      sizeAttenuation: false,
    });

    return new THREE.Points(geo, mat);
  }

  // ---------- Pulse ----------
  function createPulse(x, y, color) {
    const geo = new THREE.RingGeometry(6, 8, 32);
    const mat = new THREE.MeshBasicMaterial({ color, transparent: true, opacity: 1, side: THREE.DoubleSide });
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.set(x, y, 1);
    return mesh;
  }

  // ---------- Data processing ----------
  function hardResync(ms) {
    destState.clear();
    originState.clear();
    countrySet.clear();
    liveArcs = [];
    processedThrough = -1;

    // Clear dynamic objects
    while (arcGroup.children.length) arcGroup.remove(arcGroup.children[0]);
    while (dotGroup.children.length) dotGroup.remove(dotGroup.children[0]);
    while (particleGroup.children.length) particleGroup.remove(particleGroup.children[0]);
    arcMeshes = [];
    particleSystems = [];
    pulseMeshes = [];
    highlightRings.forEach(r => { scene.remove(r); r.geometry.dispose(); r.material.dispose(); });
    highlightRings = [];
    originDots.clear();
    destDots.clear();
    displayedLeaders = 0;
    displayedCountries = 0;

    for (let i = 0; i < events.length; i++) {
      if (events[i]._fireMs > ms) break;
      processEvent(events[i], i, ms);
    }
    recomputeStats();
    rebuildDots();
  }

  function syncToTime(ms) {
    if (ms < playState.currentTimeMs) {
      playState.currentTimeMs = ms;
      hardResync(ms);
      return;
    }
    for (let i = processedThrough + 1; i < events.length; i++) {
      if (events[i]._fireMs > ms) break;
      processEvent(events[i], i, ms);
    }
    playState.currentTimeMs = ms;
    recomputeStats();
  }

  function processEvent(ev, idx, currentMs) {
    processedThrough = idx;
    const isVirt = isVirtualEvent(ev);

    const oKey = ev.city;
    const o = originState.get(oKey) || { lon: ev.lon, lat: ev.lat, cum: 0, isVirtual: isVirt };
    o.cum = ev._cityCum;
    o.lon = ev.lon; o.lat = ev.lat; o.isVirtual = isVirt;
    o.lastFireMs = ev._fireMs;   // most recent training at this origin (for virtual fade)
    originState.set(oKey, o);

    const ageAtNow = currentMs - ev._fireMs;

    // Pulse rings on training fire — removed per design call (read as a target
    // / throbbing reticle). Dots alone now mark the event; createPulse and the
    // pulseMeshes loop are left in place but no new pulses are spawned.

    // Arcs and destinations
    ev.arcs.forEach((a, j) => {
      const dKey = a.label || a.country;
      const d = destState.get(dKey) || { lon: a.lon, lat: a.lat, cum: 0, country: a.country };
      d.cum = Math.max(d.cum, a.cum_leaders);
      d.lon = a.lon; d.lat = a.lat;
      destState.set(dKey, d);
      countrySet.add(a.country);

      if (ageAtNow >= 0 && ageAtNow <= ARC_LIFE) {
        const p1 = [ev.lon, ev.lat];
        const p2 = [a.lon, a.lat];
        // Skip arcs that are too short to read visually (e.g. same-country state-to-state)
        const dLon = p1[0] - p2[0], dLat = p1[1] - p2[1];
        const geoDist = Math.sqrt(dLon * dLon + dLat * dLat);
        if (geoDist < 12) return; // ~12 degrees minimum
        // Skip arcs that cross the antimeridian (straight lines would cut across the whole map)
        if (Math.abs(dLon) > 180) return;
        const arcData = createArcGeometry(p1, p2);
        if (arcData) {
          const colors = getColors();
          const mat = createArcMaterial(colors.arc, 1.0);
          const mesh = new THREE.Mesh(arcData.geo, mat);
          mesh.position.z = 2;
          arcGroup.add(mesh);

          // Glow (same geometry, lower opacity, behind)
          const glowGeo = createArcGeometry(p1, p2);
          let glowMesh = null;
          if (glowGeo) {
            const glowMat = createGlowMaterial(colors.arc);
            glowMesh = new THREE.Mesh(glowGeo.geo, glowMat);
            glowMesh.position.z = 1.5;
            arcGroup.add(glowMesh);
          }

          // Particles
          const particles = createParticles(arcData.path, colors.arc);
          particles.position.z = 5;
          particleGroup.add(particles);

          arcMeshes.push({
            id: `arc-${idx}-${j}`,
            mesh, glowMesh, particles,
            born: ev._fireMs,
            path: arcData.path,
          });
        }
      }
    });
  }

  function recomputeStats() {
    let leaders = 0;
    for (let i = 0; i <= processedThrough; i++) leaders += events[i].leaders;
    stats.leaders = leaders;
    stats.countries = countrySet.size;
  }

  // Collapse per-label dest state (which is state-level for some countries) into
  // one entry per country so the dot reflects the country's full training count.
  // Position is the leader-weighted centroid of the country's labels.
  function buildCountryDestState() {
    const m = new Map();
    destState.forEach((d) => {
      const c = m.get(d.country) || { country: d.country, cum: 0, lonSum: 0, latSum: 0, w: 0 };
      c.cum += d.cum;
      c.lonSum += d.lon * d.cum;
      c.latSum += d.lat * d.cum;
      c.w += d.cum;
      m.set(d.country, c);
    });
    m.forEach((c) => {
      c.lon = c.w > 0 ? c.lonSum / c.w : 0;
      c.lat = c.w > 0 ? c.latSum / c.w : 0;
    });
    return m;
  }

  function rebuildDots() {
    const colors = getColors();

    // Origin dots
    originState.forEach((o, key) => {
      const p = project([o.lon, o.lat]);
      if (!p) return;
      const r = originRadius(o.cum);
      const dot = createDot(p[0], p[1], r, colors.origin, o.isVirtual ? 0.45 : 0.9);
      dot.position.z = 3;
      dotGroup.add(dot);
      originDots.set(key, dot);
    });

    // Dest dots — one per country
    const countryDest = buildCountryDestState();
    countryDest.forEach((c, key) => {
      const p = project([c.lon, c.lat]);
      if (!p) return;
      const r = destRadius(c.cum);
      const dot = createDot(p[0], p[1], r, colors.dest, 0.75);
      dot.position.z = 2.5;
      dotGroup.add(dot);
      destDots.set(key, dot);
    });
  }

  // ---------- Render loop ----------
  function render() {
    const now = playState.currentTimeMs;
    const colors = getColors();

    // Update arcs
    arcMeshes = arcMeshes.filter(a => {
      const age = now - a.born;
      if (age > ARC_LIFE) {
        arcGroup.remove(a.mesh);
        if (a.glowMesh) arcGroup.remove(a.glowMesh);
        if (a.particles) particleGroup.remove(a.particles);
        a.mesh.geometry.dispose();
        a.mesh.material.dispose();
        if (a.glowMesh) { a.glowMesh.geometry.dispose(); a.glowMesh.material.dispose(); }
        if (a.particles) { a.particles.geometry.dispose(); a.particles.material.dispose(); }
        return false;
      }

      let drawProgress, opacity;
      if (age < CONFIG.arcDrawMs) {
        drawProgress = age / CONFIG.arcDrawMs;
        opacity = 1;
      } else if (age < CONFIG.arcDrawMs + CONFIG.arcHoldMs) {
        drawProgress = 1;
        opacity = 1;
      } else {
        drawProgress = 1;
        opacity = 1 - (age - CONFIG.arcDrawMs - CONFIG.arcHoldMs) / CONFIG.arcFadeMs;
      }

      a.mesh.material.uniforms.uDrawProgress.value = drawProgress;
      a.mesh.material.uniforms.uOpacity.value = opacity;
      if (a.glowMesh) {
        a.glowMesh.material.uniforms.uDrawProgress.value = drawProgress;
        a.glowMesh.material.uniforms.uOpacity.value = opacity * 0.3;
      }

      // Update particles along path
      if (a.particles && a.path.length > 1) {
        const positions = a.particles.geometry.attributes.position.array;
        for (let i = 0; i < CONFIG.particlesPerArc; i++) {
          const particleT = (drawProgress - 0.1 + i * 0.05) % 1.0;
          if (particleT < 0 || particleT > drawProgress) {
            positions[i * 3 + 2] = -999; // hide
            continue;
          }
          const idx = Math.min(a.path.length - 1, Math.floor(particleT * a.path.length));
          positions[i * 3] = a.path[idx][0];
          positions[i * 3 + 1] = a.path[idx][1];
          positions[i * 3 + 2] = 5;
        }
        a.particles.geometry.attributes.position.needsUpdate = true;
        a.particles.material.opacity = opacity * 0.9;
      }

      return true;
    });

    // Update pulses
    pulseMeshes = pulseMeshes.filter(p => {
      const age = now - p.userData.born;
      if (age > CONFIG.pulseMs) {
        dotGroup.remove(p);
        p.geometry.dispose();
        p.material.dispose();
        return false;
      }
      const t = age / CONFIG.pulseMs;
      const scale = 1 + t * 4;
      p.scale.set(scale, scale, 1);
      p.material.opacity = 1 - t;
      return true;
    });

    // Update dots (grow animation for new ones)
    const DOT_ANIM_MS = 600;
    originState.forEach((o, key) => {
      if (!originDots.has(key)) {
        const p = project([o.lon, o.lat]);
        if (!p) return;
        const r = originRadius(o.cum);
        const dot = createDot(p[0], p[1], r, colors.origin, o.isVirtual ? 0.45 : 0.9);
        dot.position.z = 3;
        dotGroup.add(dot);
        originDots.set(key, dot);
      } else {
        const dot = originDots.get(key);
        const r = originRadius(o.cum);
        const currentR = dot.geometry.parameters ? dot.geometry.parameters.radius : r;
        if (Math.abs(currentR - r) > 0.1) {
          dot.geometry.dispose();
          dot.geometry = new THREE.CircleGeometry(r, 24);
        }
      }
      // Virtual trainings have no permanent place — fade the dot out once its
      // moment passes, instead of letting it sit on the map forever.
      if (o.isVirtual) {
        const dot = originDots.get(key);
        if (dot) {
          const since = now - (o.lastFireMs || 0);
          const VIRT_HOLD = CONFIG.pulseMs + 1200;
          const VIRT_FADE = 1600;
          let op;
          if (since < 0) op = 0;
          else if (since <= VIRT_HOLD) op = 0.55;
          else op = Math.max(0, 0.55 * (1 - (since - VIRT_HOLD) / VIRT_FADE));
          dot.material.opacity = op;
          dot.visible = op > 0.01;
        }
      }
    });

    const countryDest = buildCountryDestState();
    countryDest.forEach((c, key) => {
      if (!destDots.has(key)) {
        const p = project([c.lon, c.lat]);
        if (!p) return;
        const r = destRadius(c.cum);
        const dot = createDot(p[0], p[1], r, colors.dest, 0.75);
        dot.position.z = 2.5;
        dotGroup.add(dot);
        destDots.set(key, dot);
      } else {
        const dot = destDots.get(key);
        const r = destRadius(c.cum);
        const currentR = dot.geometry.parameters ? dot.geometry.parameters.radius : r;
        if (Math.abs(currentR - r) > 0.1) {
          dot.geometry.dispose();
          dot.geometry = new THREE.CircleGeometry(r, 24);
        }
      }
    });

    // Animate dot entrance (elastic ease)
    const animateDots = (dotsMap) => {
      dotsMap.forEach((dot) => {
        if (!dot.userData.animating) return;
        const age = now - dot.userData.birthTime;
        if (age >= DOT_ANIM_MS) {
          dot.scale.set(1, 1, 1);
          dot.userData.animating = false;
        } else {
          const t = age / DOT_ANIM_MS;
          const s = elasticOut(t);
          dot.scale.set(s, s, 1);
        }
      });
    };
    animateDots(originDots);
    animateDots(destDots);

    // Animate highlight rings
    const perfNow = performance.now();
    highlightRings = highlightRings.filter(ring => {
      const age = perfNow - ring.userData.birthTime;
      const dur = ring.userData.duration;
      if (age > dur) {
        scene.remove(ring);
        ring.geometry.dispose();
        ring.material.dispose();
        return false;
      }
      const t = age / dur;
      // Fade in for first 20%, hold, fade out last 30%
      let opacity;
      if (t < 0.2) opacity = t / 0.2;
      else if (t < 0.7) opacity = 1;
      else opacity = 1 - (t - 0.7) / 0.3;
      ring.material.opacity = opacity * 0.6;
      // Expand slightly
      const scale = 1 + t * 0.5;
      ring.scale.set(scale, scale, 1);
      return true;
    });

    // Org layer — reveal each marker mid-way through its founding year, so a
    // branch founded the same year trainings began appears after the first
    // trainings rather than sitting on the map at time zero.
    const orgYear = yearAt(now);
    const ORG_ANIM_MS = 600;
    orgMarkers.forEach(m => {
      if (!orgVisible || orgYear < m.revealYear) {
        m.mesh.visible = false;
        m.shownAt = null;
        return;
      }
      m.mesh.visible = true;
      if (m.shownAt === null) m.shownAt = now;
      const age = now - m.shownAt;
      const s = age >= ORG_ANIM_MS ? 1 : elasticOut(age / ORG_ANIM_MS);
      m.mesh.scale.set(s, s, 1);
    });

    // Annotations
    updateAnnotations();

    // HUD
    updateHud();

    // Render
    renderer.render(scene, camera);
  }

  // ---------- Annotations ----------
  function updateAnnotations() {
    const currentYear = yearAt(playState.currentTimeMs);

    ANNOTATIONS.forEach(a => {
      // Reveal once the playhead passes
      if (currentYear >= a.year && !a.revealed) {
        a.revealed = true;
        // Geographic highlight rings disabled — they expanded/throbbed and
        // read as a target reticle, like the old training pulses.

        // Show milestone text above year, then fade out. The final beat dwells
        // less (it otherwise lingers at the end of playback).
        if (milestoneEl) {
          const isLast = (a === ANNOTATIONS[ANNOTATIONS.length - 1]);
          milestoneEl.textContent = a.text;
          milestoneEl.style.opacity = "1";
          if (milestoneTimer) clearTimeout(milestoneTimer);
          milestoneTimer = setTimeout(() => {
            milestoneEl.style.opacity = "0";
          }, isLast ? 3000 : 5000);
        }
      }
      // If scrubbed backwards, hide future annotations
      if (currentYear < a.year) {
        a.revealed = false;
      }
    });
  }

  // ---------- HUD ----------
  let yearEl, yearSubEl, leadersEl, countriesEl, milestoneEl;
  let scrubEl, scrubFillEl, playBtn, playIcon;
  let displayedLeaders = 0, displayedCountries = 0;
  let activeMilestone = null, milestoneTimer = null;

  function setupHud() {
    yearEl = document.getElementById("year-display");
    yearSubEl = document.getElementById("year-sub");
    leadersEl = document.getElementById("stat-leaders");
    countriesEl = document.getElementById("stat-countries");
    scrubEl = document.getElementById("scrub");
    scrubFillEl = document.getElementById("scrub-fill");
    playBtn = document.getElementById("play-btn");
    playIcon = document.getElementById("play-icon");

    scrubEl.min = 0;
    scrubEl.max = TOTAL_MS;
    scrubEl.step = 50;
    scrubEl.value = 0;

    let wasPlaying = false;
    scrubEl.addEventListener("pointerdown", () => { wasPlaying = playState.playing; playState.playing = false; });
    scrubEl.addEventListener("input", (e) => {
      syncToTime(+e.target.value);
      playState.finishedExtraMs = 0;
      render();
    });
    scrubEl.addEventListener("pointerup", () => { if (wasPlaying) playState.playing = true; });
    scrubEl.addEventListener("change", () => { if (wasPlaying) playState.playing = true; });

    // Year ticks
    const ticksEl = document.getElementById("scrub-ticks");
    ticksEl.innerHTML = "";
    const startYear = Math.ceil(YEAR0);
    const endYear = Math.floor(YEAR1);
    for (let y = startYear; y <= endYear; y++) {
      if (y % 5 !== 0 && y !== startYear && y !== endYear) continue;
      const t = (y - YEAR0) / TOTAL_YEARS;
      const tick = document.createElement("div");
      tick.className = "scrub-tick";
      tick.style.left = (t * 100) + "%";
      tick.textContent = String(y);
      ticksEl.appendChild(tick);
    }

    // Play/pause with delay
    playBtn.addEventListener("click", () => {
      if (playState.currentTimeMs >= TOTAL_MS && !playState.playing) {
        playState.currentTimeMs = 0;
        hardResync(0);
        playState.finishedExtraMs = 0;
      }
      if (!playState.playing) {
        setTimeout(() => {
          playState.playing = true;
          updatePlayIcon();
        }, 3000);
      } else {
        playState.playing = false;
        updatePlayIcon();
      }
    });

    // Org layer toggle
    const orgToggle = document.getElementById("org-toggle");
    if (orgToggle) {
      orgToggle.classList.toggle("active", orgVisible);
      orgToggle.addEventListener("click", () => {
        orgVisible = !orgVisible;
        orgToggle.classList.toggle("active", orgVisible);
      });
    }

  }

  function updatePlayIcon() {
    if (playState.playing) {
      playIcon.innerHTML = '<rect x="2" y="1" width="3.5" height="14" /><rect x="8.5" y="1" width="3.5" height="14" />';
    } else {
      playIcon.innerHTML = '<path d="M0 0 L14 8 L0 16 Z" />';
    }
    playIcon.setAttribute("viewBox", "0 0 14 16");
  }

  function updateHud() {
    const yFloat = yearAt(playState.currentTimeMs);
    const yInt = Math.min(Math.floor(YEAR1), Math.max(Math.floor(YEAR0), Math.floor(yFloat)));
    yearEl.textContent = String(yInt);
    // Month removed from the HUD (distracting); year only.
    if (yearSubEl) yearSubEl.textContent = "";

    // Smooth number counting — lerp toward target
    const lerpSpeed = 0.12;
    const targetLeaders = stats.leaders;
    const targetCountries = stats.countries;
    displayedLeaders += (targetLeaders - displayedLeaders) * lerpSpeed;
    displayedCountries += (targetCountries - displayedCountries) * lerpSpeed;
    // Snap when very close
    if (Math.abs(targetLeaders - displayedLeaders) < 1) displayedLeaders = targetLeaders;
    if (Math.abs(targetCountries - displayedCountries) < 1) displayedCountries = targetCountries;
    leadersEl.textContent = Math.round(displayedLeaders).toLocaleString();
    countriesEl.textContent = Math.round(displayedCountries).toLocaleString();

    if (scrubEl && document.activeElement !== scrubEl) {
      scrubEl.value = playState.currentTimeMs;
    }
    const pct = Math.min(100, (playState.currentTimeMs / TOTAL_MS) * 100);
    scrubFillEl.style.width = pct + "%";
  }

  // ---------- Animation loop ----------
  function loop(ts) {
    if (!playState.lastFrameTs) playState.lastFrameTs = ts;
    const dt = ts - playState.lastFrameTs;
    playState.lastFrameTs = ts;

    if (playState.playing) {
      const advance = dt * playState.speed;
      let next = playState.currentTimeMs + advance;
      if (next >= TOTAL_MS) {
        if (playState.currentTimeMs < TOTAL_MS) syncToTime(TOTAL_MS);
        playState.currentTimeMs = next;
        playState.finishedExtraMs = next - TOTAL_MS;
        if (playState.finishedExtraMs >= ARC_LIFE) {
          playState.playing = false;
          updatePlayIcon();
          playState.currentTimeMs = TOTAL_MS;
        }
      } else {
        syncToTime(next);
      }
    }

    render();
    requestAnimationFrame(loop);
  }

  // ---------- Boot ----------
  async function boot() {
    initThree();

    const [rawEvents, geo, org] = await Promise.all([
      fetch("data/events_v2.json").then(r => r.json()),
      fetch("data/countries-110m.geojson").then(r => r.json()),
      fetch("data/org.json").then(r => r.json()).catch(() => null),
    ]);

    events = rawEvents.map(e => {
      return e;
    });

    countries = geo.features;
    orgData = org;

    const dates = events.map(e => new Date(e.date));
    const minDate = new Date(Math.min(...dates));
    const maxDate = new Date(Math.max(...dates));
    YEAR0 = minDate.getUTCFullYear() + (minDate.getUTCMonth() / 12);
    const maxYear = maxDate.getUTCFullYear() + (maxDate.getUTCMonth() / 12) + (1 / 12);
    YEAR1 = Math.max(2025 + 11/12, maxYear);
    TOTAL_YEARS = YEAR1 - YEAR0;
    TOTAL_MS = TOTAL_YEARS * CONFIG.yearMs;

    // Pre-compute
    const cityRunSums = new Map();
    events.forEach(e => {
      e._fireMs = eventFireMs(e);
      const prev = cityRunSums.get(e.city) || 0;
      e._cityCum = prev + e.leaders;
      cityRunSums.set(e.city, e._cityCum);
    });
    events.sort((a, b) => a._fireMs - b._fireMs);

    // Compute annotation ms
    ANNOTATIONS.forEach(a => { a.ms = (a.year - YEAR0) * CONFIG.yearMs; });

    rebuildStaticLayers();
    setupHud();
    setupMobileTouch();
    syncToTime(0);
    requestAnimationFrame(loop);
  }

  // ---------- Mobile Touch ----------
  function setupMobileTouch() {
    if (!isMobile()) return;

    const canvas = renderer.domElement;

    // Tap anywhere on the map canvas to toggle play/pause
    let touchStart = null;
    canvas.addEventListener("touchstart", (e) => {
      if (e.touches.length === 1) {
        touchStart = { x: e.touches[0].clientX, y: e.touches[0].clientY, t: Date.now() };
      }
    }, { passive: true });

    canvas.addEventListener("touchend", (e) => {
      if (!touchStart) return;
      const dt = Date.now() - touchStart.t;
      // Quick tap (< 300ms, minimal movement) = play/pause
      if (dt < 300) {
        const touch = e.changedTouches[0];
        const dx = Math.abs(touch.clientX - touchStart.x);
        const dy = Math.abs(touch.clientY - touchStart.y);
        if (dx < 15 && dy < 15) {
          playState.playing = !playState.playing;
          updatePlayIcon();
        }
      }
      touchStart = null;
    }, { passive: true });
  }

  // ---------- Public API ----------
  window.__mapApi = {
    setTheme(t) {
      theme = t;
      document.body.classList.toggle("dark", t === "dark");
      document.body.classList.toggle("light", t !== "dark");
      if (renderer) {
        rebuildStaticLayers();
        hardResync(playState.currentTimeMs);
      }
    },
    setDotScale(s) {
      dotScale = s;
    },
    setShowLabels(v) {
      showLabels = !!v;
    },
    setArcStyle(s) {
      arcStyle = s;
      if (renderer) hardResync(playState.currentTimeMs);
    },
    setYearMs(ms) {
      const oldFrac = TOTAL_MS ? playState.currentTimeMs / TOTAL_MS : 0;
      CONFIG.yearMs = ms;
      if (!events.length) return;
      TOTAL_MS = TOTAL_YEARS * CONFIG.yearMs;
      events.forEach(e => { e._fireMs = eventFireMs(e); });
      events.sort((a, b) => a._fireMs - b._fireMs);
      ANNOTATIONS.forEach(a => { a.ms = (a.year - YEAR0) * CONFIG.yearMs; });
      if (scrubEl) scrubEl.max = TOTAL_MS;
      const newMs = oldFrac * TOTAL_MS;
      playState.currentTimeMs = newMs;
      hardResync(newMs);
    },
    restart() {
      playState.currentTimeMs = 0;
      playState.finishedExtraMs = 0;
      ANNOTATIONS.forEach(a => { a.revealed = false; if (a.el) a.el.style.opacity = "0"; });
      hardResync(0);
      playState.playing = true;
      updatePlayIcon();
    },
    setColors({ origin, dest, arc }) {
      colorOverrides.origin = origin || "";
      colorOverrides.dest = dest || "";
      colorOverrides.arc = arc || "";
      if (renderer) hardResync(playState.currentTimeMs);
    },
    setOrgLayer(v) {
      orgVisible = !!v;
      const t = document.getElementById("org-toggle");
      if (t) t.classList.toggle("active", orgVisible);
    },
  };

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", boot);
  } else {
    boot();
  }
})();
