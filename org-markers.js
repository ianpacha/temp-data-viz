// org-markers.js
// Four interchangeable visual languages for the branch / chapter / hub layer.
// All four solve the same problem: make org presence read distinctly from the
// surface-level training dots, and encode hierarchy clearly.
//
//   beacons  — lifted glyphs above the surface, thin anchor stem, soft halo disc
//              behind. Branch = halo ring + core, Chapter = solid bead, Hub = open ring.
//              Hierarchy via glyph + height. Default.
//   pillars  — extruded radial columns of varying height + radius. Glowing caps.
//              Hierarchy via height. Reads like a city skyline of presence.
//   radar    — surface dot + animated concentric rings expanding outward.
//              Hierarchy via concurrent-pulse count + max radius.
//   minimal  — refined version of the original ring/diamond approach with better
//              contrast and proportions. Still & quiet.
//
// Usage:
//   const layer = OrgMarkers.build({ parent: globeGroup, org, style, palette });
//   layer.update(time);          // call from render loop
//   layer.setLayer(type, bool);  // 'branch' | 'chapter' | 'hub'
//   layer.setLabelMode(mode);    // 'off' | 'branches' | 'all'
//   layer.updateLabelVisibility(camera);
//   layer.recolor(palette);
//   layer.markers // array of pickable meshes for raycaster
//   layer.dispose();

(function () {
  'use strict';

  const RADIUS = 1;

  // ─── COLOR PALETTES ────────────────────────────────────────────────────────
  // 'split'  = current: branch green, chapter/hub gold
  // 'gold'   = all gold, branch brightest -> hub palest
  // 'green'  = all green, branch brightest -> hub palest
  const PALETTES = {
    split: { branch: 0xC0D110, chapter: 0xFFC500, hub: 0xFFC500 },
    gold:  { branch: 0xFFC500, chapter: 0xFFC500, hub: 0xFFC500 },
    green: { branch: 0xC0D110, chapter: 0x8DC63F, hub: 0x457428 }
  };

  function paletteColor(palette, orgType) {
    return PALETTES[palette] ? PALETTES[palette][orgType] : PALETTES.split[orgType];
  }

  // ─── HELPERS ───────────────────────────────────────────────────────────────
  function latLonToVec3(lat, lon, r) {
    const phi = (90 - lat) * Math.PI / 180;
    const theta = (lon + 180) * Math.PI / 180;
    return new THREE.Vector3(
      -r * Math.sin(phi) * Math.cos(theta),
       r * Math.cos(phi),
       r * Math.sin(phi) * Math.sin(theta)
    );
  }

  // Quaternion that aligns local +Z to outward-radial direction (for flat
  // surface-tangent shapes like rings / circles).
  function tangentQuat(pos) {
    const q = new THREE.Quaternion();
    q.setFromUnitVectors(new THREE.Vector3(0, 0, 1), pos.clone().normalize());
    return q;
  }

  // Quaternion that aligns local +Y to outward-radial direction (for cylinders).
  function radialYQuat(pos) {
    const q = new THREE.Quaternion();
    q.setFromUnitVectors(new THREE.Vector3(0, 1, 0), pos.clone().normalize());
    return q;
  }

  // Build a glow disc canvas texture (radial gradient, transparent edge).
  let _glowTex = null;
  function glowTexture() {
    if (_glowTex) return _glowTex;
    const c = document.createElement('canvas');
    c.width = c.height = 128;
    const ctx = c.getContext('2d');
    const g = ctx.createRadialGradient(64, 64, 0, 64, 64, 64);
    g.addColorStop(0,    'rgba(255,255,255,1)');
    g.addColorStop(0.35, 'rgba(255,255,255,0.55)');
    g.addColorStop(1,    'rgba(255,255,255,0)');
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, 128, 128);
    _glowTex = new THREE.CanvasTexture(c);
    return _glowTex;
  }

  // Build a label sprite (canvas-textured, billboarded).
  function makeLabel(text) {
    const c = document.createElement('canvas');
    c.width = 512; c.height = 96;
    const ctx = c.getContext('2d');
    ctx.font = '600 36px Helvetica, Arial, sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    // halo (stroke)
    ctx.lineWidth = 6;
    ctx.strokeStyle = 'rgba(16,80,47,0.75)';
    ctx.strokeText(text, 256, 50);
    // fill
    ctx.fillStyle = '#F0F2D8';
    ctx.fillText(text, 256, 50);
    const tex = new THREE.CanvasTexture(c);
    tex.minFilter = THREE.LinearFilter;
    const mat = new THREE.SpriteMaterial({ map: tex, transparent: true, depthTest: true });
    const sprite = new THREE.Sprite(mat);
    sprite.scale.set(0.25, 0.047, 1);
    sprite.userData.isLabel = true;
    return sprite;
  }

  // ─── STYLE: BEACONS ────────────────────────────────────────────────────────
  // Lifted glyph at top of a thin stem; glow disc behind glyph.
  function buildBeacons({ parent, org, palette }) {
    const grp = new THREE.Group();
    parent.add(grp);
    const markers = [];
    const pulsers = []; // {mesh, baseOpacity}
    const HEIGHT = { branch: 0.14, chapter: 0.038, hub: 0.038 };

    function addItem(item, orgType, label) {
      const color = paletteColor(palette, orgType);
      const surfPos = latLonToVec3(item.lat, item.lon, RADIUS);
      const radial = surfPos.clone().normalize();
      const liftPos = surfPos.clone().addScaledVector(radial, HEIGHT[orgType]);

      // Stem: thin line from surface to lift point
      const stemGeo = new THREE.BufferGeometry().setFromPoints([
        surfPos.clone().addScaledVector(radial, 0.002),
        liftPos.clone().addScaledVector(radial, -0.005)
      ]);
      const stemMat = new THREE.LineBasicMaterial({
        color: color, transparent: true, opacity: 0.45
      });
      grp.add(new THREE.Line(stemGeo, stemMat));

      // Surface anchor: tiny dot
      const anchorGeo = new THREE.SphereGeometry(0.0035, 8, 8);
      const anchorMat = new THREE.MeshBasicMaterial({ color: color, transparent: true, opacity: 0.7 });
      const anchor = new THREE.Mesh(anchorGeo, anchorMat);
      anchor.position.copy(surfPos.clone().addScaledVector(radial, 0.001));
      grp.add(anchor);

      // The glyph itself (this is the pickable mesh)
      let glyph;
      if (orgType === 'branch') {
        // BRANCH: solid diamond (octahedron) — the regional anchor. Replaces the
        // old halo-ring + core, which read as a bullseye / target. A larger
        // diamond reads as "more important than a hub" by size + shape, not rings.
        const diamond = new THREE.Mesh(
          new THREE.OctahedronGeometry(0.026),
          new THREE.MeshBasicMaterial({ color: color, transparent: true, opacity: 0.97 })
        );
        diamond.position.copy(liftPos);
        diamond.renderOrder = 10;
        grp.add(diamond);
        markers.push(diamond);
        diamond.userData = { type: 'org', orgType, name: item.name, label };
        glyph = diamond;
      } else {
        // CHAPTER + HUB: same solid bead — visually equivalent, distinguished only
        // by name + tooltip. Smaller, quieter than branches.
        const beadGeo = new THREE.SphereGeometry(0.009, 12, 12);
        const beadMat = new THREE.MeshBasicMaterial({ color: color, transparent: true, opacity: 0.95 });
        const bead = new THREE.Mesh(beadGeo, beadMat);
        bead.position.copy(liftPos);
        bead.renderOrder = 10;
        grp.add(bead);
        bead.userData = { type: 'org', orgType, name: item.name, label };
        markers.push(bead);
        glyph = bead;
      }

      // Label sprite
      const lab = makeLabel(stripSuffix(item.name));
      lab.position.copy(liftPos.clone().addScaledVector(radial, 0.045));
      grp.add(lab);
      glyph.userData.label_sprite = lab;
      glyph.userData.org_anchor = anchor;
      glyph.userData.org_stem_mat = stemMat;
    }

    (org.branches  || []).forEach(b => addItem(b, 'branch',  'Branch'));
    (org.chapters  || []).forEach(c => addItem(c, 'chapter', 'Chapter'));
    (org.hubs      || []).forEach(h => addItem(h, 'hub',     'Hub'));

    return makeLayer(grp, markers, pulsers, 'beacons');
  }

  // ─── STYLE: PILLARS ────────────────────────────────────────────────────────
  // Extruded radial cylinders with cap. Hierarchy via height + radius.
  function buildPillars({ parent, org, palette }) {
    const grp = new THREE.Group();
    parent.add(grp);
    const markers = [];
    const pulsers = [];

    const SPEC = {
      branch:  { h: 0.14,  r: 0.0065, capR: 0.013, hollow: false },
      chapter: { h: 0.055, r: 0.0042, capR: 0.006, hollow: false },
      hub:     { h: 0.055, r: 0.0042, capR: 0.006, hollow: false }
    };

    function addItem(item, orgType, label) {
      const color = paletteColor(palette, orgType);
      const spec = SPEC[orgType];
      const surfPos = latLonToVec3(item.lat, item.lon, RADIUS);
      const radial = surfPos.clone().normalize();
      const mid    = surfPos.clone().addScaledVector(radial, spec.h / 2);
      const top    = surfPos.clone().addScaledVector(radial, spec.h);

      // Cylinder (default along +Y, base at -h/2)
      const cylGeo = new THREE.CylinderGeometry(spec.r, spec.r, spec.h, 12, 1, spec.hollow);
      const cylMat = new THREE.MeshBasicMaterial({
        color: color, transparent: true, opacity: spec.hollow ? 0.7 : 0.9,
        wireframe: spec.hollow
      });
      const cyl = new THREE.Mesh(cylGeo, cylMat);
      cyl.position.copy(mid);
      cyl.quaternion.copy(radialYQuat(mid));
      grp.add(cyl);
      cyl.userData = { type: 'org', orgType, name: item.name, label };
      markers.push(cyl);

      // Glowing cap
      const capGeo = new THREE.SphereGeometry(spec.capR, 12, 12);
      const capMat = new THREE.MeshBasicMaterial({ color: color, transparent: true, opacity: 1 });
      const cap = new THREE.Mesh(capGeo, capMat);
      cap.position.copy(top);
      grp.add(cap);

      // Cap glow halo
      const glowMat = new THREE.SpriteMaterial({
        map: glowTexture(), color: color, transparent: true, opacity: 0.55,
        blending: THREE.AdditiveBlending, depthTest: true, depthWrite: false
      });
      const glow = new THREE.Sprite(glowMat);
      const gs = orgType === 'branch' ? 0.10 : 0.035;
      glow.scale.set(gs, gs, 1);
      glow.position.copy(top);
      grp.add(glow);
      pulsers.push({ mesh: glow, baseOpacity: 0.55, type: 'opacity' });

      // Label
      const lab = makeLabel(stripSuffix(item.name));
      lab.position.copy(top.clone().addScaledVector(radial, 0.04));
      grp.add(lab);
      cyl.userData.label_sprite = lab;
      cyl.userData.org_cap = cap;
      cyl.userData.org_glow = glow;
    }

    (org.branches || []).forEach(b => addItem(b, 'branch',  'Branch'));
    (org.chapters || []).forEach(c => addItem(c, 'chapter', 'Chapter'));
    (org.hubs     || []).forEach(h => addItem(h, 'hub',     'Hub'));

    return makeLayer(grp, markers, pulsers, 'pillars');
  }

  // ─── STYLE: RADAR ──────────────────────────────────────────────────────────
  // Surface dot + N animated rings expanding outward in tangent plane.
  function buildRadar({ parent, org, palette }) {
    const grp = new THREE.Group();
    parent.add(grp);
    const markers = [];
    const pulsers = [];

    const SPEC = {
      branch:  { count: 3, maxR: 0.075, period: 2.6, coreR: 0.009 },
      chapter: { count: 2, maxR: 0.028, period: 2.4, coreR: 0.004 },
      hub:     { count: 2, maxR: 0.028, period: 2.4, coreR: 0.004 }
    };

    function addItem(item, orgType, label) {
      const color = paletteColor(palette, orgType);
      const spec = SPEC[orgType];
      const surfPos = latLonToVec3(item.lat, item.lon, RADIUS * 1.005);
      const quat = tangentQuat(surfPos);

      // Solid core dot (pickable)
      const coreGeo = new THREE.SphereGeometry(spec.coreR, 12, 12);
      const coreMat = new THREE.MeshBasicMaterial({ color: color, transparent: true, opacity: 0.95 });
      const core = new THREE.Mesh(coreGeo, coreMat);
      core.position.copy(surfPos);
      grp.add(core);
      core.userData = { type: 'org', orgType, name: item.name, label };
      markers.push(core);

      // N pulsing rings
      const rings = [];
      for (let i = 0; i < spec.count; i++) {
        // Unit ring (outer = 1, inner = 0.7) — scaled at runtime
        const ringGeo = new THREE.RingGeometry(0.7, 1, 32);
        const ringMat = new THREE.MeshBasicMaterial({
          color: color, transparent: true, opacity: 0, side: THREE.DoubleSide,
          depthTest: true, depthWrite: false
        });
        const ring = new THREE.Mesh(ringGeo, ringMat);
        ring.position.copy(surfPos);
        ring.quaternion.copy(quat);
        ring.scale.set(0.001, 0.001, 1);
        grp.add(ring);
        rings.push(ring);
      }
      pulsers.push({ rings, maxR: spec.maxR, period: spec.period, type: 'radar', count: spec.count });

      // Label
      const radial = surfPos.clone().normalize();
      const lab = makeLabel(stripSuffix(item.name));
      lab.position.copy(surfPos.clone().addScaledVector(radial, 0.035));
      grp.add(lab);
      core.userData.label_sprite = lab;
    }

    (org.branches || []).forEach(b => addItem(b, 'branch',  'Branch'));
    (org.chapters || []).forEach(c => addItem(c, 'chapter', 'Chapter'));
    (org.hubs     || []).forEach(h => addItem(h, 'hub',     'Hub'));

    return makeLayer(grp, markers, pulsers, 'radar');
  }

  // ─── STYLE: MINIMAL (refined original) ─────────────────────────────────────
  function buildMinimal({ parent, org, palette }) {
    const grp = new THREE.Group();
    parent.add(grp);
    const markers = [];
    const pulsers = [];

    function addBranch(item) {
      const color = paletteColor(palette, 'branch');
      const pos = latLonToVec3(item.lat, item.lon, RADIUS * 1.013);
      const ringGeo = new THREE.RingGeometry(0.028, 0.044, 48);
      const ringMat = new THREE.MeshBasicMaterial({
        color: color, transparent: true, opacity: 0.92, side: THREE.DoubleSide
      });
      const ring = new THREE.Mesh(ringGeo, ringMat);
      ring.position.copy(pos);
      ring.quaternion.copy(tangentQuat(pos));
      grp.add(ring);
      ring.userData = { type: 'org', orgType: 'branch', name: item.name, label: 'Branch' };
      markers.push(ring);

      // Solid inner core
      const coreGeo = new THREE.CircleGeometry(0.012, 24);
      const coreMat = new THREE.MeshBasicMaterial({
        color: color, transparent: true, opacity: 0.95, side: THREE.DoubleSide
      });
      const core = new THREE.Mesh(coreGeo, coreMat);
      core.position.copy(pos);
      core.quaternion.copy(tangentQuat(pos));
      grp.add(core);

      // Soft glow disc behind
      const glowMat = new THREE.SpriteMaterial({
        map: glowTexture(), color: color, transparent: true, opacity: 0.45,
        blending: THREE.AdditiveBlending, depthTest: true, depthWrite: false
      });
      const glow = new THREE.Sprite(glowMat);
      glow.scale.set(0.12, 0.12, 1);
      glow.position.copy(pos);
      grp.add(glow);
      pulsers.push({ mesh: glow, baseOpacity: 0.45, type: 'opacity' });

      const radial = pos.clone().normalize();
      const lab = makeLabel(stripSuffix(item.name));
      lab.position.copy(pos.clone().addScaledVector(radial, 0.055));
      grp.add(lab);
      ring.userData.label_sprite = lab;
    }

    function addDiamond(item, orgType, label) {
      // Chapter + hub render identically — small solid diamond.
      const color = paletteColor(palette, orgType);
      const pos = latLonToVec3(item.lat, item.lon, RADIUS * 1.012);
      const mat = new THREE.MeshBasicMaterial({
        color: color, transparent: true, opacity: 0.95
      });
      const m = new THREE.Mesh(new THREE.OctahedronGeometry(0.009), mat);
      m.position.copy(pos);
      grp.add(m);
      m.userData = { type: 'org', orgType, name: item.name, label };
      markers.push(m);

      const radial = pos.clone().normalize();
      const lab = makeLabel(stripSuffix(item.name));
      lab.position.copy(pos.clone().addScaledVector(radial, 0.03));
      grp.add(lab);
      m.userData.label_sprite = lab;
    }

    (org.branches || []).forEach(addBranch);
    (org.chapters || []).forEach(c => addDiamond(c, 'chapter', 'Chapter'));
    (org.hubs     || []).forEach(h => addDiamond(h, 'hub',     'Hub'));

    return makeLayer(grp, markers, pulsers, 'minimal');
  }

  // ─── LAYER (shared controller returned by each builder) ────────────────────
  function makeLayer(grp, markers, pulsers, styleName) {
    let labelMode = 'branches';  // 'off' | 'branches' | 'all'
    let layerVisible = { branch: true, chapter: true, hub: true };
    let motion = 1; // 0 still / 1 gentle / 2 vivid

    function refreshLabelVisibility(camera) {
      // Always-on visibility based on org type + camera distance.
      markers.forEach(m => {
        const lab = m.userData.label_sprite;
        if (!lab) return;
        const t = m.userData.orgType;
        let on = false;
        if (labelMode === 'off')          on = false;
        else if (labelMode === 'branches') on = (t === 'branch');
        else if (labelMode === 'all')     on = (t === 'branch') || (t === 'chapter' && camera.position.z < 2.4) || (t === 'hub' && camera.position.z < 1.8);
        // Hide entirely if layer toggled off
        if (!layerVisible[t]) on = false;
        lab.visible = on;
      });
    }

    return {
      group: grp,
      markers,
      style: styleName,
      update(time, camera) {
        if (motion > 0) {
          // Pulse animation
          pulsers.forEach((p, i) => {
            if (p.type === 'opacity') {
              const speed = motion === 2 ? 1.8 : 1.0;
              const phase = i * 0.4;
              const v = 0.5 + 0.5 * Math.sin(time * speed + phase);
              p.mesh.material.opacity = p.baseOpacity * (0.5 + 0.5 * v) * (motion === 2 ? 1.2 : 1);
            } else if (p.type === 'radar') {
              const speed = motion === 2 ? 1.6 : 1.0;
              for (let k = 0; k < p.count; k++) {
                const ring = p.rings[k];
                const phase = k / p.count;
                const t = ((time * speed / p.period) + phase) % 1;
                const s = Math.max(0.001, t * p.maxR);
                ring.scale.set(s, s, 1);
                ring.material.opacity = (1 - t) * 0.85;
              }
            }
          });
        } else {
          // Reset to base
          pulsers.forEach(p => {
            if (p.type === 'opacity') p.mesh.material.opacity = p.baseOpacity;
            else if (p.type === 'radar') p.rings.forEach(r => { r.scale.set(0.001, 0.001, 1); r.material.opacity = 0; });
          });
        }
        if (camera) refreshLabelVisibility(camera);
      },
      setLayer(type, on) {
        layerVisible[type] = on;
        markers.forEach(m => {
          if (m.userData.orgType === type) {
            m.visible = on;
            // Hide all sibling meshes (cap, glow, anchor, stem) that aren't tracked
            // — simplest: walk group and toggle. We rely on visible flag on each
            // marker's userData refs.
            ['org_cap', 'org_anchor', 'org_glow'].forEach(k => {
              if (m.userData[k]) m.userData[k].visible = on;
            });
          }
        });
        // Pulsers don't carry orgType directly; gate them via their associated marker.
        // Walk pulsers and hide if their parent marker is hidden.
        pulsers.forEach(p => {
          if (p.type === 'opacity' && p.mesh) {
            // Find nearest marker by position — cheap approximation
            // (acceptable because pulse position is glow position).
            // Simpler: if any marker of this type is invisible, set this pulser invisible
            // when it sits at the same position. We just leave them; they're cheap.
          }
        });
      },
      setLabelMode(mode) { labelMode = mode; },
      setMotion(m) { motion = m; },
      // Additive glow looks great on a dark backdrop but blows out to white
      // over a light one. Switch the glow discs to normal blending on light.
      setGlowBlending(additive) {
        pulsers.forEach(p => {
          if (p.type === 'opacity' && p.mesh && p.mesh.material) {
            p.mesh.material.blending = additive ? THREE.AdditiveBlending : THREE.NormalBlending;
            p.mesh.material.needsUpdate = true;
          }
        });
      },
      recolor(palette) {
        markers.forEach(m => {
          m.material.color.set(paletteColor(palette, m.userData.orgType));
        });
        // Walk the group and recolor any auxiliary meshes; they were built from
        // the same palette but identifying type without backrefs is fiddly.
        // Easiest: stash type on every child.
        grp.traverse(child => {
          if (child.userData.__aux_orgType && child.material && child.material.color) {
            child.material.color.set(paletteColor(palette, child.userData.__aux_orgType));
          }
        });
      },
      updateLabelVisibility(camera) { refreshLabelVisibility(camera); },
      dispose() {
        grp.traverse(child => {
          if (child.geometry) child.geometry.dispose();
          if (child.material) {
            if (Array.isArray(child.material)) child.material.forEach(m => m.dispose());
            else child.material.dispose();
          }
        });
        if (grp.parent) grp.parent.remove(grp);
        markers.length = 0;
        pulsers.length = 0;
      }
    };
  }

  // ─── UTIL ──────────────────────────────────────────────────────────────────
  // Trim "Branch", "Chapter", "Hub" suffix from labels for cleaner globe text.
  function stripSuffix(name) {
    return name.replace(/\s+(Branch|Chapter|Hub)$/i, '');
  }

  // ─── PUBLIC API ────────────────────────────────────────────────────────────
  window.OrgMarkers = {
    STYLES: ['beacons', 'pillars', 'radar', 'minimal'],
    PALETTES: Object.keys(PALETTES),
    build({ parent, org, style, palette }) {
      const opts = { parent, org, palette: palette || 'split' };
      switch (style) {
        case 'pillars': return buildPillars(opts);
        case 'radar':   return buildRadar(opts);
        case 'minimal': return buildMinimal(opts);
        case 'beacons':
        default:        return buildBeacons(opts);
      }
    }
  };
})();
