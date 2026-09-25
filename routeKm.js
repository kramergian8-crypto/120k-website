/*
 * routeKm.js — standalone, dependency-free route-projection tracker.
 *
 * Given a known route (array of [lat, lon, ele, cumKm]) and a stream of
 * noisy GPS fixes, this module maintains a monotonic "distance along the
 * route" (km) for a runner, resolving the ambiguity that arises when the
 * route passes close to itself (e.g. Interlaken is visited twice, ~60 km
 * apart, on roads that can be < 500 m apart) or when start and finish
 * coincide (Thun).
 *
 * Core idea: instead of asking "what is the single closest point on the
 * route to this GPS fix" (ambiguous near self-intersections), we ask
 * "what is the closest point *within a plausible window* of where we
 * already are". The window is derived from the last known km and the
 * elapsed time since the last update, using a generous max running speed
 * (vmax). This turns a global nearest-point search into a local one, so
 * the two Interlaken passes and the shared start/finish resolve
 * correctly as long as we have *some* prior position (from seed,
 * seedFromSpur, or a previous update).
 *
 * Two operating modes:
 *  - "seeking" (right after seed(appKm), before we've locked onto the
 *    route from a real GPS fix): search window is wide (appKm +/- 10 km,
 *    per spec), and the very first on-route match may correct km in
 *    either direction (even backwards) since the seed was only a rough
 *    guess, not a confirmed projection.
 *  - "locked" (after a successful on-route match, or after
 *    seedFromSpur): search window is tight
 *    [lastKm-0.3, lastKm+vmax*dt+0.5] km, and km is strictly monotonic
 *    non-decreasing.
 *
 * Browser usage:
 *   <script src="routeKm.js"></script>
 *   const tracker = new window.RouteKm(routeFull, opts);
 *
 * Node / CommonJS usage:
 *   const RouteKm = require('./routeKm.js');
 *   const tracker = new RouteKm(routeFull, opts);
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) {
    module.exports = factory();
  } else {
    root.RouteKm = factory();
  }
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  var EARTH_R = 6371008.8; // mean earth radius, meters (IUGG)
  var DEG2RAD = Math.PI / 180;

  // ---- geometry helpers -----------------------------------------------

  // Equirectangular projection is plenty accurate over the small lat span
  // of this route (< 1 degree) and much cheaper than full haversine for
  // every segment test. We use a local reference latitude for the
  // longitude scale factor.
  function makeProjector(refLatDeg) {
    var cosRef = Math.cos(refLatDeg * DEG2RAD);
    return function (lat, lon) {
      return {
        x: lon * DEG2RAD * cosRef * EARTH_R,
        y: lat * DEG2RAD * EARTH_R
      };
    };
  }

  // Closest point on segment [ax,ay]-[bx,by] to point [px,py], projected
  // (planar) coordinates. Returns {x,y,t} where t in [0,1] is the
  // fractional position along the segment.
  function closestOnSegment(px, py, ax, ay, bx, by) {
    var vx = bx - ax,
      vy = by - ay;
    var len2 = vx * vx + vy * vy;
    var t;
    if (len2 < 1e-9) {
      t = 0;
    } else {
      t = ((px - ax) * vx + (py - ay) * vy) / len2;
      if (t < 0) t = 0;
      else if (t > 1) t = 1;
    }
    return { x: ax + t * vx, y: ay + t * vy, t: t };
  }

  function clamp(v, lo, hi) {
    return v < lo ? lo : v > hi ? hi : v;
  }

  // ---- main constructor -------------------------------------------------

  /**
   * @param {Array<Array<number>>} routeFull  array of [lat, lon, ele, cumKm]
   * @param {Object} [opts]
   * @param {number} [opts.densifyM=10]   target spacing (meters) after
   *        densifying long segments. Set 0/Infinity to disable densifying.
   * @param {number} [opts.gridCellM=200] spatial grid cell size (meters),
   *        used only for the coarse global search (cold start / seeking).
   * @param {number} [opts.vmax=4]        plausible max running speed, m/s.
   * @param {number} [opts.onRouteM=75]   max distance (m) to accept a fix
   *        as "on route" for advancing km.
   * @param {number} [opts.offRouteM=150] distance (m) beyond which a fix
   *        counts as "off route" (starts the off-route timer).
   * @param {number} [opts.offRouteHoldS=120] seconds off-route before we
   *        stop trusting the route projection and fall back to appKm.
   * @param {number} [opts.seedWindowKm=10] +/- window (km) used while
   *        "seeking" (right after seed()) to (re)acquire the route.
   */
  function RouteKm(routeFull, opts) {
    opts = opts || {};
    this.vmax = opts.vmax || 4; // m/s: generous ceiling for a trail/road runner
    this.onRouteM = opts.onRouteM != null ? opts.onRouteM : 75;
    this.offRouteM = opts.offRouteM != null ? opts.offRouteM : 150;
    this.offRouteHoldS =
      opts.offRouteHoldS != null ? opts.offRouteHoldS : 120;
    this.densifyM = opts.densifyM != null ? opts.densifyM : 10;
    this.gridCellM = opts.gridCellM || 200;
    this.seedWindowKm = opts.seedWindowKm != null ? opts.seedWindowKm : 10;

    if (!routeFull || routeFull.length < 2) {
      throw new Error('RouteKm: routeFull must have >= 2 points');
    }

    // reference latitude for the equirectangular projector: mean lat
    var latSum = 0;
    for (var i = 0; i < routeFull.length; i++) latSum += routeFull[i][0];
    this._project = makeProjector(latSum / routeFull.length);

    this.routeLength = routeFull[routeFull.length - 1][3];

    this._buildPoints(routeFull);
    this._buildGrid();

    // runtime state
    this.lastKm = null; // last accepted km (monotonic once locked)
    this.lastT = null; // unix seconds of last update
    this.lastSource = 'none';
    this._locked = false; // true once we trust lastKm as a real projection
    this._seedCenterKm = null; // center of the wide search window while seeking
    this._offRouteSinceT = null; // when the current off-route streak began
  }

  // Build the (possibly densified) polyline of {lat,lon,x,y,km} points,
  // monotonic in km, used for windowed segment search.
  RouteKm.prototype._buildPoints = function (routeFull) {
    var pts = [];
    var self = this;

    function pushPoint(lat, lon, km) {
      var p = self._project(lat, lon);
      pts.push({ lat: lat, lon: lon, x: p.x, y: p.y, km: km });
    }

    for (var i = 0; i < routeFull.length; i++) {
      var cur = routeFull[i];
      pushPoint(cur[0], cur[1], cur[3]);

      if (i < routeFull.length - 1) {
        var next = routeFull[i + 1];
        var segKm = next[3] - cur[3];
        var segM = segKm * 1000;
        if (this.densifyM && segM > this.densifyM * 1.5) {
          var n = Math.floor(segM / this.densifyM);
          for (var k = 1; k < n; k++) {
            var f = k / n;
            var lat = cur[0] + (next[0] - cur[0]) * f;
            var lon = cur[1] + (next[1] - cur[1]) * f;
            var km = cur[3] + segKm * f;
            pushPoint(lat, lon, km);
          }
        }
      }
    }

    this.points = pts; // sorted by km ascending, index i <-> segment [i, i+1]
  };

  // Coarse uniform grid over projected x/y, mapping cell -> list of point
  // indices, used only for global searches (cold start / seeking).
  RouteKm.prototype._buildGrid = function () {
    var cell = this.gridCellM;
    var grid = Object.create(null);
    var minX = Infinity,
      minY = Infinity;
    for (var i = 0; i < this.points.length; i++) {
      var p = this.points[i];
      if (p.x < minX) minX = p.x;
      if (p.y < minY) minY = p.y;
    }
    this._gridMinX = minX;
    this._gridMinY = minY;

    for (var j = 0; j < this.points.length; j++) {
      var pt = this.points[j];
      var cx = Math.floor((pt.x - minX) / cell);
      var cy = Math.floor((pt.y - minY) / cell);
      var key = cx + '_' + cy;
      if (!grid[key]) grid[key] = [];
      grid[key].push(j);
    }
    this._grid = grid;
    this._gridCell = cell;
  };

  // Full (grid-accelerated) nearest-point search over the *entire* route.
  // Used only for true cold-start (update() called with no seed at all).
  RouteKm.prototype._globalNearest = function (lat, lon) {
    var p = this._project(lat, lon);
    var cx = Math.floor((p.x - this._gridMinX) / this._gridCell);
    var cy = Math.floor((p.y - this._gridMinY) / this._gridCell);

    var best = null;
    var foundAtRadius = -1;
    var maxRadius = 2000; // generous upper bound on ring expansion
    for (var r = 0; r <= maxRadius; r++) {
      var any = false;
      for (var dx = -r; dx <= r; dx++) {
        for (var dy = -r; dy <= r; dy++) {
          if (Math.max(Math.abs(dx), Math.abs(dy)) !== r) continue; // ring only
          var key = (cx + dx) + '_' + (cy + dy);
          var list = this._grid[key];
          if (!list) continue;
          any = true;
          for (var i = 0; i < list.length; i++) {
            var res = this._nearestOnSegmentsAround(list[i], p.x, p.y);
            if (res && (!best || res.distM < best.distM)) best = res;
          }
        }
      }
      if (best && foundAtRadius < 0) foundAtRadius = r;
      if (foundAtRadius >= 0 && r >= foundAtRadius + 1) break;
      if (!any && foundAtRadius >= 0) break;
    }

    if (!best) best = this._bruteNearest(p.x, p.y);
    return best;
  };

  RouteKm.prototype._nearestOnSegmentsAround = function (idx, px, py) {
    var best = null;
    var pts = this.points;
    for (var s = idx - 1; s <= idx; s++) {
      if (s < 0 || s >= pts.length - 1) continue;
      var a = pts[s],
        b = pts[s + 1];
      var c = closestOnSegment(px, py, a.x, a.y, b.x, b.y);
      var dx = px - c.x,
        dy = py - c.y;
      var distM = Math.sqrt(dx * dx + dy * dy);
      if (!best || distM < best.distM) {
        best = { distM: distM, km: a.km + (b.km - a.km) * c.t };
      }
    }
    return best;
  };

  RouteKm.prototype._bruteNearest = function (px, py) {
    var best = null;
    var pts = this.points;
    for (var s = 0; s < pts.length - 1; s++) {
      var a = pts[s],
        b = pts[s + 1];
      var c = closestOnSegment(px, py, a.x, a.y, b.x, b.y);
      var dx = px - c.x,
        dy = py - c.y;
      var distM = Math.sqrt(dx * dx + dy * dy);
      if (!best || distM < best.distM) {
        best = { distM: distM, km: a.km + (b.km - a.km) * c.t };
      }
    }
    return best;
  };

  // Binary search: first point index with km >= target.
  RouteKm.prototype._kmLowerBound = function (km) {
    var pts = this.points;
    var lo = 0,
      hi = pts.length - 1;
    while (lo < hi) {
      var mid = (lo + hi) >> 1;
      if (pts[mid].km < km) lo = mid + 1;
      else hi = mid;
    }
    return lo;
  };

  // Search all segments whose km lies in [loKm, hiKm] and return the
  // closest one to (px, py) (already-projected point). Internal helper
  // shared by the windowed and wide (seeking) searches.
  RouteKm.prototype._nearestInRange = function (px, py, loKm, hiKm) {
    var pts = this.points;
    var n = pts.length;
    var loIdx = Math.max(0, this._kmLowerBound(loKm) - 1);
    var hiIdx = Math.min(n - 1, this._kmLowerBound(hiKm) + 1);
    var best = null;
    for (var s = loIdx; s < hiIdx; s++) {
      var a = pts[s],
        b = pts[s + 1];
      var c = closestOnSegment(px, py, a.x, a.y, b.x, b.y);
      var dx = px - c.x,
        dy = py - c.y;
      var distM = Math.sqrt(dx * dx + dy * dy);
      if (!best || distM < best.distM) {
        best = { distM: distM, km: a.km + (b.km - a.km) * c.t };
      }
    }
    return best;
  };

  // Windowed nearest-point search used once locked. Only considers
  // segments whose km lies in [kmMin, kmMax], clamped to [0, routeLength]
  // — deliberately NOT wrapped across the start/finish point. The route
  // is run once, start-to-finish; it never continues past routeLength or
  // before 0. Clamping (rather than wrapping the search to the "other
  // end") is what actually solves "near finish must not snap back to
  // ~0" / "near start must not jump to ~120.6": the shared start/finish
  // location in Thun means a whole ~300m stretch near the very end of
  // the route runs within a few meters of a stretch near the very
  // beginning (finish chute alongside the start corridor) — a genuine
  // near-self-intersection, just like the double Interlaken pass. If we
  // let the window peek across the boundary "just in case", we would
  // pull in exactly that confusable stretch. Restricting the window to
  // the current end of the route (no wraparound) keeps the two ends
  // disjoint from each other's search space at all times.
  RouteKm.prototype._nearestInWindow = function (lat, lon, kmMin, kmMax) {
    var p = this._project(lat, lon);
    var loKm = Math.max(0, kmMin);
    var hiKm = Math.min(this.routeLength, kmMax);
    return this._nearestInRange(p.x, p.y, loKm, hiKm);
  };

  // ---- public API --------------------------------------------------------

  /**
   * Cold-start seed from the app's own (rough) km estimate, e.g. a
   * previously-saved value. This does NOT do a route search itself —
   * it just marks where update() should start looking. The tracker
   * enters "seeking" mode: the *next* update() call searches a wide
   * window (appKm +/- seedWindowKm, default 10 km) and, on its first
   * on-route match, snaps to that match (even if it's behind appKm —
   * the seed is only a rough guess, not a confirmed projection). Once
   * that first match happens, the tracker "locks" and behaves like any
   * other update() from then on (tight window, monotonic non-decreasing).
   *
   * @param {number} appKm
   * @returns {{km:number, source:string}}
   */
  RouteKm.prototype.seed = function (appKm) {
    var km = clamp(appKm, 0, this.routeLength);
    this.lastKm = km;
    this.lastT = null;
    this.lastSource = 'app';
    this._locked = false;
    this._seedCenterKm = km;
    this._offRouteSinceT = null;
    return { km: km, source: 'app' };
  };

  /**
   * Cold-start seed by replaying a spur history (5-minute buffer of
   * [[lat,lon,unixSec], ...], ascending time). The first fix is located
   * with a full-route (grid-accelerated) nearest search since there is
   * no prior km yet; every subsequent fix is fed through the normal
   * windowed update(), which locks on and self-corrects using the
   * direction of travel within the spur. Leaves the tracker "locked".
   *
   * @param {Array<Array<number>>} spur  [[lat,lon,unixSec], ...] ascending time
   * @returns {{km:number, distM:number|null, onRoute:boolean, source:string}}
   */
  RouteKm.prototype.seedFromSpur = function (spur) {
    if (!spur || spur.length === 0) {
      return { km: this.lastKm || 0, distM: null, onRoute: false, source: 'none' };
    }

    var first = spur[0];
    var g = this._globalNearest(first[0], first[1]);
    this.lastKm = g.km;
    this.lastT = first[2];
    this.lastSource = g.distM <= this.onRouteM ? 'route' : 'app';
    this._locked = true;
    this._offRouteSinceT = g.distM <= this.offRouteM ? null : first[2];

    var result = {
      km: this.lastKm,
      distM: g.distM,
      onRoute: g.distM <= this.onRouteM,
      source: this.lastSource
    };

    for (var i = 1; i < spur.length; i++) {
      var fx = spur[i];
      result = this.update(fx[0], fx[1], fx[2], null);
    }
    return result;
  };

  /**
   * Feed one GPS fix and get back the current along-route km.
   *
   * @param {number} lat
   * @param {number} lon
   * @param {number} unixSec        fix timestamp, seconds
   * @param {number} [appKm]        the app's own (independent) km guess.
   *        Used (a) to (re)center the wide search window while
   *        "seeking", and (b) as the off-route fallback signal once
   *        locked. May be omitted/undefined.
   * @returns {{km:number, distM:number|null, onRoute:boolean, source:string}}
   */
  RouteKm.prototype.update = function (lat, lon, unixSec, appKm) {
    // True cold start (no seed() / seedFromSpur() ever called): do one
    // full-route search to get on the board, then behave as "seeking"
    // would (we don't have a confirmed lock yet either).
    if (this.lastKm === null) {
      var g0 = this._globalNearest(lat, lon);
      var onRoute0 = g0.distM <= this.onRouteM;
      this.lastKm = g0.km;
      this.lastT = unixSec;
      this.lastSource = onRoute0 ? 'route' : 'none';
      this._locked = onRoute0;
      this._seedCenterKm = g0.km;
      this._offRouteSinceT = g0.distM <= this.offRouteM ? null : unixSec;
      return { km: this.lastKm, distM: g0.distM, onRoute: onRoute0, source: this.lastSource };
    }

    var dt = this.lastT != null ? Math.max(0, unixSec - this.lastT) : 3;

    // --- seeking mode: wide window, first on-route match wins (can move
    // km in either direction since we have no confirmed lock yet). ---
    if (!this._locked) {
      var center =
        appKm != null && isFinite(appKm) ? appKm : this._seedCenterKm != null ? this._seedCenterKm : this.lastKm;
      var wLo = Math.max(0, center - this.seedWindowKm);
      var wHi = Math.min(this.routeLength, center + this.seedWindowKm);
      var wNear = this._nearestInRange(this._project(lat, lon).x, this._project(lat, lon).y, wLo, wHi);

      this.lastT = unixSec;
      this._seedCenterKm = center;

      if (wNear && wNear.distM <= this.onRouteM) {
        this.lastKm = clamp(wNear.km, 0, this.routeLength);
        this.lastSource = 'route';
        this._locked = true;
        this._offRouteSinceT = null;
        return { km: this.lastKm, distM: wNear.distM, onRoute: true, source: 'route' };
      }

      // No confident match yet: report the app's own estimate (clamped
      // to route bounds) without locking, so a caller with no route fix
      // yet still gets a sane number.
      var fallback = clamp(center, 0, this.routeLength);
      this.lastKm = fallback;
      this.lastSource = 'app';
      return { km: fallback, distM: wNear ? wNear.distM : null, onRoute: false, source: 'app' };
    }

    // --- locked mode: tight window, monotonic non-decreasing. ---
    // Search window: generous by spec (lastKm-0.3 .. lastKm+vmax*dt+0.5)
    // so we don't lose the point under noise or after a short gap (the
    // window widens automatically with dt for longer gaps). The window
    // is only where we LOOK; how much km we actually CREDIT is capped
    // separately (see capAdvanceKm below) — that is the real anti-jump
    // guard.
    var vmaxDtKm = (this.vmax * dt) / 1000;
    var windowAheadKm = vmaxDtKm + 0.5;
    var capAdvanceKm = vmaxDtKm + 0.2;

    var kmMin = this.lastKm - 0.3;
    var kmMax = this.lastKm + windowAheadKm;

    var nearest = this._nearestInWindow(lat, lon, kmMin, kmMax);
    var distM = nearest ? nearest.distM : Infinity;
    var onRoute = distM <= this.onRouteM;
    var offRoute = distM > this.offRouteM;

    if (offRoute) {
      if (this._offRouteSinceT === null) this._offRouteSinceT = unixSec;
    } else {
      this._offRouteSinceT = null;
    }
    var offRouteDurationS = this._offRouteSinceT !== null ? unixSec - this._offRouteSinceT : 0;

    var km, source;

    if (offRoute && offRouteDurationS > this.offRouteHoldS) {
      // Off-route for longer than offRouteHoldS (a real detour, not just
      // a bad fix): stop trusting the route projection. Exact rule:
      //   km = max(lastKm, clamp(appKm, lastKm, lastKm + vmax*dt))
      // i.e. we never go backwards, and we never let the app's km jump
      // further ahead in one tick than physically possible since the
      // last update (vmax*dt). If appKm isn't supplied we just hold at
      // lastKm. source is 'app' to signal the route projection is not
      // being trusted right now.
      var appClamped = this.lastKm;
      if (appKm != null && isFinite(appKm)) {
        appClamped = clamp(appKm, this.lastKm, this.lastKm + vmaxDtKm);
      }
      km = Math.max(this.lastKm, appClamped);
      source = 'app';
    } else if (onRoute && nearest.km >= this.lastKm - 1e-9) {
      // Normal case: on-route (<=75m) and not behind lastKm -> accept,
      // capped at capAdvanceKm so one noisy/jumpy fix can't leap far.
      var rawAdvance = nearest.km - this.lastKm;
      var cappedAdvance = Math.min(rawAdvance, capAdvanceKm);
      km = this.lastKm + Math.max(0, cappedAdvance);
      source = 'route';
    } else {
      // Either not close enough (<=75m) to credit forward motion, or the
      // windowed nearest point is behind lastKm (GPS noise while slow/
      // stationary, or at a tight corner) -> hold, never decrease.
      km = this.lastKm;
      source = distM <= this.offRouteM ? 'route' : 'none';
    }

    km = clamp(km, 0, this.routeLength);

    this.lastKm = km;
    this.lastT = unixSec;
    this.lastSource = source;

    return { km: km, distM: isFinite(distM) ? distM : null, onRoute: onRoute, source: source };
  };

  RouteKm.prototype.getState = function () {
    return { km: this.lastKm, t: this.lastT, source: this.lastSource, locked: this._locked };
  };

  return RouteKm;
});
